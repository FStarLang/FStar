open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
  
let (bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e  -> fun t  -> normalize [] e t 
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e  -> fun t  -> FStar_TypeChecker_Normalize.unfold_whnf e t 
let (tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  FStar_TypeChecker_Normalize.term_to_string 
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun e  ->
    fun t  ->
      FStar_Syntax_Print.term_to_string' e.FStar_TypeChecker_Env.dsenv t
  
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g  ->
    let uu____65 =
      let uu____66 = FStar_Tactics_Types.goal_env g  in
      let uu____67 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____66 uu____67  in
    FStar_Tactics_Types.goal_with_type g uu____65
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____92 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____92
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____117 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____117
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____149 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____149
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____162 =
      let uu____163 = FStar_Tactics_Types.goal_env g  in
      let uu____164 = FStar_Tactics_Types.goal_type g  in
      whnf uu____163 uu____164  in
    FStar_Syntax_Util.un_squash uu____162
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____173 = get_phi g  in FStar_Option.isSome uu____173 
let (print : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg  ->
    (let uu____189 =
       let uu____191 = FStar_Options.silent ()  in
       Prims.op_Negation uu____191  in
     if uu____189 then tacprint msg else ());
    FStar_Tactics_Monad.ret ()
  
let (debugging : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____204  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps  ->
         let uu____212 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         FStar_Tactics_Monad.ret uu____212)
  
let (dump : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg  ->
    FStar_Tactics_Monad.mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____236 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          FStar_Tactics_Printing.do_dump_proofstate uu____236 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let fail1 :
  'Auu____244 .
    Prims.string -> Prims.string -> 'Auu____244 FStar_Tactics_Monad.tac
  =
  fun msg  ->
    fun x  ->
      let uu____261 = FStar_Util.format1 msg x  in
      FStar_Tactics_Monad.fail uu____261
  
let fail2 :
  'Auu____272 .
    Prims.string ->
      Prims.string -> Prims.string -> 'Auu____272 FStar_Tactics_Monad.tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____296 = FStar_Util.format2 msg x y  in
        FStar_Tactics_Monad.fail uu____296
  
let fail3 :
  'Auu____309 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> 'Auu____309 FStar_Tactics_Monad.tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____340 = FStar_Util.format3 msg x y z  in
          FStar_Tactics_Monad.fail uu____340
  
let fail4 :
  'Auu____355 .
    Prims.string ->
      Prims.string ->
        Prims.string ->
          Prims.string -> Prims.string -> 'Auu____355 FStar_Tactics_Monad.tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____393 = FStar_Util.format4 msg x y z w  in
            FStar_Tactics_Monad.fail uu____393
  
let catch :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (Prims.exn,'a) FStar_Util.either FStar_Tactics_Monad.tac
  =
  fun t  ->
    FStar_Tactics_Monad.mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____428 = FStar_Tactics_Monad.run t ps  in
         match uu____428 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___70_452 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___70_452.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___70_452.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___70_452.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___70_452.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___70_452.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___70_452.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___70_452.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___70_452.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___70_452.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___70_452.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___70_452.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (Prims.exn,'a) FStar_Util.either FStar_Tactics_Monad.tac
  =
  fun t  ->
    FStar_Tactics_Monad.mk_tac
      (fun ps  ->
         let uu____491 = FStar_Tactics_Monad.run t ps  in
         match uu____491 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac :
  'a .
    'a FStar_Tactics_Monad.tac ->
      'a FStar_Pervasives_Native.option FStar_Tactics_Monad.tac
  =
  fun t  ->
    let uu____539 = catch t  in
    FStar_Tactics_Monad.bind uu____539
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 ->
             FStar_Tactics_Monad.ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____566 ->
             FStar_Tactics_Monad.ret FStar_Pervasives_Native.None)
  
let trytac_exn :
  'a .
    'a FStar_Tactics_Monad.tac ->
      'a FStar_Pervasives_Native.option FStar_Tactics_Monad.tac
  =
  fun t  ->
    FStar_Tactics_Monad.mk_tac
      (fun ps  ->
         try
           (fun uu___96_598  ->
              match () with
              | () ->
                  let uu____603 = trytac t  in
                  FStar_Tactics_Monad.run uu____603 ps) ()
         with
         | FStar_Errors.Err (uu____619,msg) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____625  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____631,msg,uu____633) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____638  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____667 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____667
         then
           let uu____671 = FStar_Syntax_Print.term_to_string t1  in
           let uu____673 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____671
             uu____673
         else ());
        (try
           (fun uu___116_684  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____692 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____692
                    then
                      let uu____696 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____698 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____700 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____696
                        uu____698 uu____700
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Tactics_Monad.ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____711 =
                          FStar_Tactics_Monad.add_implicits
                            g.FStar_TypeChecker_Common.implicits
                           in
                        FStar_Tactics_Monad.bind uu____711
                          (fun uu____716  -> FStar_Tactics_Monad.ret true))))
             ()
         with
         | FStar_Errors.Err (uu____726,msg) ->
             FStar_Tactics_Monad.mlog
               (fun uu____732  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____735  -> FStar_Tactics_Monad.ret false)
         | FStar_Errors.Error (uu____738,msg,r) ->
             FStar_Tactics_Monad.mlog
               (fun uu____746  ->
                  let uu____747 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____747)
               (fun uu____751  -> FStar_Tactics_Monad.ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____780  ->
             (let uu____782 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____782
              then
                (FStar_Options.push ();
                 (let uu____787 =
                    FStar_Options.set_options
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____791 = __do_unify env t1 t2  in
              FStar_Tactics_Monad.bind uu____791
                (fun r  ->
                   (let uu____802 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____802 then FStar_Options.pop () else ());
                   FStar_Tactics_Monad.ret r)))
  
let (do_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uvs1 = FStar_Syntax_Free.uvars_uncached t1  in
        let uu____834 = do_unify env t1 t2  in
        FStar_Tactics_Monad.bind uu____834
          (fun r  ->
             if r
             then
               let uvs2 = FStar_Syntax_Free.uvars_uncached t1  in
               let uu____852 =
                 let uu____854 = FStar_Util.set_eq uvs1 uvs2  in
                 Prims.op_Negation uu____854  in
               (if uu____852
                then FStar_Tactics_Monad.ret false
                else FStar_Tactics_Monad.ret true)
             else FStar_Tactics_Monad.ret false)
  
let (set_solution :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal  ->
    fun solution  ->
      let uu____885 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____885 with
      | FStar_Pervasives_Native.Some uu____890 ->
          let uu____891 =
            let uu____893 =
              FStar_Tactics_Printing.goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____893  in
          FStar_Tactics_Monad.fail uu____891
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           FStar_Tactics_Monad.ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun goal  ->
    fun solution  ->
      let uu____914 = FStar_Tactics_Types.goal_env goal  in
      let uu____915 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____914 solution uu____915
  
let (solve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      FStar_Tactics_Monad.mlog
        (fun uu____935  ->
           let uu____936 =
             let uu____938 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____938  in
           let uu____939 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____936 uu____939)
        (fun uu____944  ->
           let uu____945 = trysolve goal solution  in
           FStar_Tactics_Monad.bind uu____945
             (fun b  ->
                if b
                then
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____957  ->
                       FStar_Tactics_Monad.remove_solved_goals)
                else
                  (let uu____960 =
                     let uu____962 =
                       let uu____964 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____964 solution  in
                     let uu____965 =
                       let uu____967 = FStar_Tactics_Types.goal_env goal  in
                       let uu____968 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____967 uu____968  in
                     let uu____969 =
                       let uu____971 = FStar_Tactics_Types.goal_env goal  in
                       let uu____972 = FStar_Tactics_Types.goal_type goal  in
                       tts uu____971 uu____972  in
                     FStar_Util.format3 "%s does not solve %s : %s" uu____962
                       uu____965 uu____969
                      in
                   FStar_Tactics_Monad.fail uu____960)))
  
let (solve' :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal  ->
    fun solution  ->
      let uu____989 = set_solution goal solution  in
      FStar_Tactics_Monad.bind uu____989
        (fun uu____993  ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
             (fun uu____995  -> FStar_Tactics_Monad.remove_solved_goals))
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1004 = FStar_Syntax_Util.un_squash t1  in
    match uu____1004 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____1016 =
          let uu____1017 = FStar_Syntax_Subst.compress t'1  in
          uu____1017.FStar_Syntax_Syntax.n  in
        (match uu____1016 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1022 -> false)
    | uu____1024 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1037 = FStar_Syntax_Util.un_squash t  in
    match uu____1037 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1048 =
          let uu____1049 = FStar_Syntax_Subst.compress t'  in
          uu____1049.FStar_Syntax_Syntax.n  in
        (match uu____1048 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1054 -> false)
    | uu____1056 -> false
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t  ->
    let uu____1072 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps  ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g  ->
                (let uu____1081 =
                   let uu____1082 = FStar_Tactics_Types.goal_type g  in
                   uu____1082.FStar_Syntax_Syntax.pos  in
                 let uu____1085 =
                   let uu____1091 =
                     let uu____1093 =
                       FStar_Tactics_Printing.goal_to_string ""
                         FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1093
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1091)  in
                 FStar_Errors.log_issue uu____1081 uu____1085);
                solve' g t))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tadmit_t") uu____1072
  
let (fresh : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1116  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___202_1127 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___202_1127.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (uu___202_1127.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___202_1127.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___202_1127.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___202_1127.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___202_1127.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___202_1127.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___202_1127.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___202_1127.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___202_1127.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___202_1127.FStar_Tactics_Types.local_state)
           }  in
         let uu____1129 = FStar_Tactics_Monad.set ps1  in
         FStar_Tactics_Monad.bind uu____1129
           (fun uu____1134  ->
              let uu____1135 = FStar_BigInt.of_int_fs n1  in
              FStar_Tactics_Monad.ret uu____1135))
  
let (curms : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1143  ->
    let uu____1146 =
      let uu____1147 = FStar_Util.now_ms ()  in
      FStar_All.pipe_right uu____1147 FStar_BigInt.of_int_fs  in
    FStar_Tactics_Monad.ret uu____1146
  
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e  ->
    fun t  ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps  ->
           FStar_Tactics_Monad.mlog
             (fun uu____1193  ->
                let uu____1194 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1194)
             (fun uu____1199  ->
                let e1 =
                  let uu___211_1201 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___211_1201.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___211_1201.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___211_1201.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___211_1201.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___211_1201.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___211_1201.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___211_1201.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___211_1201.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___211_1201.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___211_1201.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___211_1201.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___211_1201.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___211_1201.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___211_1201.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___211_1201.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___211_1201.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___211_1201.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___211_1201.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___211_1201.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___211_1201.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___211_1201.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___211_1201.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___211_1201.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___211_1201.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___211_1201.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___211_1201.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___211_1201.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___211_1201.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___211_1201.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___211_1201.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___211_1201.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___211_1201.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___211_1201.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___211_1201.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___211_1201.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___211_1201.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___211_1201.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___211_1201.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___211_1201.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___211_1201.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___211_1201.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___211_1201.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___211_1201.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___211_1201.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___211_1201.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___211_1201.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___215_1213  ->
                     match () with
                     | () ->
                         let uu____1222 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         FStar_Tactics_Monad.ret uu____1222) ()
                with
                | FStar_Errors.Err (uu____1249,msg) ->
                    let uu____1253 = tts e1 t  in
                    let uu____1255 =
                      let uu____1257 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____1257
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1253 uu____1255 msg
                | FStar_Errors.Error (uu____1267,msg,uu____1269) ->
                    let uu____1272 = tts e1 t  in
                    let uu____1274 =
                      let uu____1276 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____1276
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1272 uu____1274 msg))
  
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e  ->
    fun t  ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps  ->
           FStar_Tactics_Monad.mlog
             (fun uu____1329  ->
                let uu____1330 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____1330)
             (fun uu____1335  ->
                let e1 =
                  let uu___232_1337 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___232_1337.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___232_1337.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___232_1337.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___232_1337.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___232_1337.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___232_1337.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___232_1337.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___232_1337.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___232_1337.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___232_1337.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___232_1337.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___232_1337.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___232_1337.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___232_1337.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___232_1337.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___232_1337.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___232_1337.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___232_1337.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___232_1337.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___232_1337.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___232_1337.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___232_1337.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___232_1337.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___232_1337.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___232_1337.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___232_1337.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___232_1337.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___232_1337.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___232_1337.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___232_1337.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___232_1337.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___232_1337.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___232_1337.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___232_1337.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___232_1337.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___232_1337.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___232_1337.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___232_1337.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___232_1337.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___232_1337.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___232_1337.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___232_1337.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___232_1337.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___232_1337.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___232_1337.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___232_1337.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___236_1352  ->
                     match () with
                     | () ->
                         let uu____1361 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____1361 with
                          | (t1,lc,g) ->
                              FStar_Tactics_Monad.ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu____1399,msg) ->
                    let uu____1403 = tts e1 t  in
                    let uu____1405 =
                      let uu____1407 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____1407
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1403 uu____1405 msg
                | FStar_Errors.Error (uu____1417,msg,uu____1419) ->
                    let uu____1422 = tts e1 t  in
                    let uu____1424 =
                      let uu____1426 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____1426
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1422 uu____1424 msg))
  
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e  ->
    fun t  ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps  ->
           FStar_Tactics_Monad.mlog
             (fun uu____1479  ->
                let uu____1480 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_lax(%s)\n" uu____1480)
             (fun uu____1486  ->
                let e1 =
                  let uu___257_1488 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___257_1488.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___257_1488.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___257_1488.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___257_1488.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___257_1488.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___257_1488.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___257_1488.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___257_1488.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___257_1488.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___257_1488.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___257_1488.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___257_1488.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___257_1488.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___257_1488.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___257_1488.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___257_1488.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___257_1488.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___257_1488.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___257_1488.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___257_1488.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___257_1488.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___257_1488.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___257_1488.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___257_1488.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___257_1488.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___257_1488.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___257_1488.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___257_1488.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___257_1488.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___257_1488.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___257_1488.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___257_1488.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___257_1488.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___257_1488.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___257_1488.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___257_1488.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___257_1488.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___257_1488.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___257_1488.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___257_1488.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___257_1488.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___257_1488.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___257_1488.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___257_1488.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___257_1488.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___257_1488.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                let e2 =
                  let uu___260_1491 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___260_1491.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___260_1491.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___260_1491.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___260_1491.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___260_1491.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___260_1491.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___260_1491.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___260_1491.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___260_1491.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___260_1491.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___260_1491.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___260_1491.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___260_1491.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___260_1491.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___260_1491.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___260_1491.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___260_1491.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___260_1491.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___260_1491.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___260_1491.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___260_1491.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___260_1491.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___260_1491.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___260_1491.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___260_1491.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___260_1491.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___260_1491.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___260_1491.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___260_1491.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___260_1491.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___260_1491.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___260_1491.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___260_1491.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___260_1491.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___260_1491.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___260_1491.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___260_1491.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___260_1491.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___260_1491.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___260_1491.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___260_1491.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___260_1491.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___260_1491.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___260_1491.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___260_1491.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___260_1491.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___264_1503  ->
                     match () with
                     | () ->
                         let uu____1512 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         FStar_Tactics_Monad.ret uu____1512) ()
                with
                | FStar_Errors.Err (uu____1539,msg) ->
                    let uu____1543 = tts e2 t  in
                    let uu____1545 =
                      let uu____1547 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____1547
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1543 uu____1545 msg
                | FStar_Errors.Error (uu____1557,msg,uu____1559) ->
                    let uu____1562 = tts e2 t  in
                    let uu____1564 =
                      let uu____1566 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____1566
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1562 uu____1564 msg))
  
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Env.Reify;
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.UnfoldTac;
        FStar_TypeChecker_Env.Unmeta]  in
      let t1 = normalize steps e t  in is_true t1
  
let (get_guard_policy :
  unit -> FStar_Tactics_Types.guard_policy FStar_Tactics_Monad.tac) =
  fun uu____1600  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps  -> FStar_Tactics_Monad.ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy :
  FStar_Tactics_Types.guard_policy -> unit FStar_Tactics_Monad.tac) =
  fun pol  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps  ->
         FStar_Tactics_Monad.set
           (let uu___285_1619 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___285_1619.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___285_1619.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___285_1619.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___285_1619.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___285_1619.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___285_1619.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___285_1619.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___285_1619.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___285_1619.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___285_1619.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___285_1619.FStar_Tactics_Types.local_state)
            }))
  
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun pol  ->
    fun t  ->
      let uu____1644 = get_guard_policy ()  in
      FStar_Tactics_Monad.bind uu____1644
        (fun old_pol  ->
           let uu____1650 = set_guard_policy pol  in
           FStar_Tactics_Monad.bind uu____1650
             (fun uu____1654  ->
                FStar_Tactics_Monad.bind t
                  (fun r  ->
                     let uu____1658 = set_guard_policy old_pol  in
                     FStar_Tactics_Monad.bind uu____1658
                       (fun uu____1662  -> FStar_Tactics_Monad.ret r))))
  
let (getopts : FStar_Options.optionstate FStar_Tactics_Monad.tac) =
  let uu____1666 = trytac FStar_Tactics_Monad.cur_goal  in
  FStar_Tactics_Monad.bind uu____1666
    (fun uu___0_1675  ->
       match uu___0_1675 with
       | FStar_Pervasives_Native.Some g ->
           FStar_Tactics_Monad.ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____1681 = FStar_Options.peek ()  in
           FStar_Tactics_Monad.ret uu____1681)
  
let (proc_guard :
  Prims.string ->
    env -> FStar_TypeChecker_Common.guard_t -> unit FStar_Tactics_Monad.tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        FStar_Tactics_Monad.mlog
          (fun uu____1706  ->
             let uu____1707 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____1707)
          (fun uu____1712  ->
             let uu____1713 =
               FStar_Tactics_Monad.add_implicits
                 g.FStar_TypeChecker_Common.implicits
                in
             FStar_Tactics_Monad.bind uu____1713
               (fun uu____1717  ->
                  FStar_Tactics_Monad.bind getopts
                    (fun opts  ->
                       let uu____1721 =
                         let uu____1722 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____1722.FStar_TypeChecker_Common.guard_f  in
                       match uu____1721 with
                       | FStar_TypeChecker_Common.Trivial  ->
                           FStar_Tactics_Monad.ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____1726 = istrivial e f  in
                           if uu____1726
                           then FStar_Tactics_Monad.ret ()
                           else
                             FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____1739 =
                                          let uu____1745 =
                                            let uu____1747 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____1747
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____1745)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____1739);
                                       FStar_Tactics_Monad.ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1753  ->
                                           let uu____1754 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____1754)
                                        (fun uu____1759  ->
                                           let uu____1760 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts ""
                                              in
                                           FStar_Tactics_Monad.bind
                                             uu____1760
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___314_1768 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___314_1768.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___314_1768.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___314_1768.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___314_1768.FStar_Tactics_Types.label)
                                                  }  in
                                                FStar_Tactics_Monad.push_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1772  ->
                                           let uu____1773 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____1773)
                                        (fun uu____1778  ->
                                           let uu____1779 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts ""
                                              in
                                           FStar_Tactics_Monad.bind
                                             uu____1779
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___321_1787 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___321_1787.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___321_1787.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___321_1787.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___321_1787.FStar_Tactics_Types.label)
                                                  }  in
                                                FStar_Tactics_Monad.push_smt_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1791  ->
                                           let uu____1792 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____1792)
                                        (fun uu____1796  ->
                                           try
                                             (fun uu___328_1801  ->
                                                match () with
                                                | () ->
                                                    let uu____1804 =
                                                      let uu____1806 =
                                                        let uu____1808 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____1808
                                                         in
                                                      Prims.op_Negation
                                                        uu____1806
                                                       in
                                                    if uu____1804
                                                    then
                                                      FStar_Tactics_Monad.mlog
                                                        (fun uu____1815  ->
                                                           let uu____1816 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____1816)
                                                        (fun uu____1820  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else
                                                      FStar_Tactics_Monad.ret
                                                        ()) ()
                                           with
                                           | uu___327_1825 ->
                                               FStar_Tactics_Monad.mlog
                                                 (fun uu____1830  ->
                                                    let uu____1831 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____1831)
                                                 (fun uu____1835  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tcc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp FStar_Tactics_Monad.tac)
  =
  fun e  ->
    fun t  ->
      let uu____1852 =
        let uu____1855 = __tc_lax e t  in
        FStar_Tactics_Monad.bind uu____1855
          (fun uu____1875  ->
             match uu____1875 with
             | (uu____1884,lc,uu____1886) ->
                 let uu____1887 =
                   let uu____1888 = FStar_TypeChecker_Common.lcomp_comp lc
                      in
                   FStar_All.pipe_right uu____1888
                     FStar_Pervasives_Native.fst
                    in
                 FStar_Tactics_Monad.ret uu____1887)
         in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tcc") uu____1852
  
let (tc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Reflection_Data.typ FStar_Tactics_Monad.tac)
  =
  fun e  ->
    fun t  ->
      let uu____1917 =
        let uu____1922 = tcc e t  in
        FStar_Tactics_Monad.bind uu____1922
          (fun c  ->
             FStar_Tactics_Monad.ret (FStar_Syntax_Util.comp_result c))
         in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tc") uu____1917
  
let (trivial : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____1947  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal  ->
         let uu____1953 =
           let uu____1955 = FStar_Tactics_Types.goal_env goal  in
           let uu____1956 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____1955 uu____1956  in
         if uu____1953
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____1962 =
              let uu____1964 = FStar_Tactics_Types.goal_env goal  in
              let uu____1965 = FStar_Tactics_Types.goal_type goal  in
              tts uu____1964 uu____1965  in
            fail1 "Not a trivial goal: %s" uu____1962))
  
let divide :
  'a 'b .
    FStar_BigInt.t ->
      'a FStar_Tactics_Monad.tac ->
        'b FStar_Tactics_Monad.tac -> ('a * 'b) FStar_Tactics_Monad.tac
  =
  fun n1  ->
    fun l  ->
      fun r  ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun p  ->
             let uu____2016 =
               try
                 (fun uu___381_2039  ->
                    match () with
                    | () ->
                        let uu____2050 =
                          let uu____2059 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2059
                            p.FStar_Tactics_Types.goals
                           in
                        FStar_Tactics_Monad.ret uu____2050) ()
               with
               | uu___380_2070 ->
                   FStar_Tactics_Monad.fail "divide: not enough goals"
                in
             FStar_Tactics_Monad.bind uu____2016
               (fun uu____2107  ->
                  match uu____2107 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___363_2133 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___363_2133.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___363_2133.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___363_2133.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___363_2133.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___363_2133.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___363_2133.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___363_2133.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___363_2133.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___363_2133.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___363_2133.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2134 = FStar_Tactics_Monad.set lp  in
                      FStar_Tactics_Monad.bind uu____2134
                        (fun uu____2142  ->
                           FStar_Tactics_Monad.bind l
                             (fun a  ->
                                FStar_Tactics_Monad.bind
                                  FStar_Tactics_Monad.get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___369_2158 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___369_2158.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___369_2158.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___369_2158.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___369_2158.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___369_2158.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___369_2158.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___369_2158.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___369_2158.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___369_2158.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___369_2158.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____2159 =
                                       FStar_Tactics_Monad.set rp  in
                                     FStar_Tactics_Monad.bind uu____2159
                                       (fun uu____2167  ->
                                          FStar_Tactics_Monad.bind r
                                            (fun b  ->
                                               FStar_Tactics_Monad.bind
                                                 FStar_Tactics_Monad.get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___375_2183 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___375_2183.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___375_2183.FStar_Tactics_Types.all_implicits);
                                                        FStar_Tactics_Types.goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.goals
                                                             rp'.FStar_Tactics_Types.goals);
                                                        FStar_Tactics_Types.smt_goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.smt_goals
                                                             (FStar_List.append
                                                                rp'.FStar_Tactics_Types.smt_goals
                                                                p.FStar_Tactics_Types.smt_goals));
                                                        FStar_Tactics_Types.depth
                                                          =
                                                          (uu___375_2183.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___375_2183.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___375_2183.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___375_2183.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___375_2183.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___375_2183.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___375_2183.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___375_2183.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____2184 =
                                                      FStar_Tactics_Monad.set
                                                        p'
                                                       in
                                                    FStar_Tactics_Monad.bind
                                                      uu____2184
                                                      (fun uu____2192  ->
                                                         FStar_Tactics_Monad.bind
                                                           FStar_Tactics_Monad.remove_solved_goals
                                                           (fun uu____2198 
                                                              ->
                                                              FStar_Tactics_Monad.ret
                                                                (a, b)))))))))))
  
let focus : 'a . 'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac =
  fun f  ->
    let uu____2220 = divide FStar_BigInt.one f FStar_Tactics_Monad.idtac  in
    FStar_Tactics_Monad.bind uu____2220
      (fun uu____2233  ->
         match uu____2233 with | (a,()) -> FStar_Tactics_Monad.ret a)
  
let rec map :
  'a . 'a FStar_Tactics_Monad.tac -> 'a Prims.list FStar_Tactics_Monad.tac =
  fun tau  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> FStar_Tactics_Monad.ret []
         | uu____2271::uu____2272 ->
             let uu____2275 =
               let uu____2284 = map tau  in
               divide FStar_BigInt.one tau uu____2284  in
             FStar_Tactics_Monad.bind uu____2275
               (fun uu____2302  ->
                  match uu____2302 with
                  | (h,t) -> FStar_Tactics_Monad.ret (h :: t)))
  
let (seq :
  unit FStar_Tactics_Monad.tac ->
    unit FStar_Tactics_Monad.tac -> unit FStar_Tactics_Monad.tac)
  =
  fun t1  ->
    fun t2  ->
      let uu____2344 =
        FStar_Tactics_Monad.bind t1
          (fun uu____2349  ->
             let uu____2350 = map t2  in
             FStar_Tactics_Monad.bind uu____2350
               (fun uu____2358  -> FStar_Tactics_Monad.ret ()))
         in
      focus uu____2344
  
let (intro : unit -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac) =
  fun uu____2368  ->
    let uu____2371 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal  ->
           let uu____2380 =
             let uu____2387 =
               let uu____2388 = FStar_Tactics_Types.goal_env goal  in
               let uu____2389 = FStar_Tactics_Types.goal_type goal  in
               whnf uu____2388 uu____2389  in
             FStar_Syntax_Util.arrow_one uu____2387  in
           match uu____2380 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2398 =
                 let uu____2400 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2400  in
               if uu____2398
               then FStar_Tactics_Monad.fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2409 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2409 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____2425 =
                    FStar_Tactics_Monad.new_uvar "intro" env' typ'  in
                  FStar_Tactics_Monad.bind uu____2425
                    (fun uu____2442  ->
                       match uu____2442 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____2466 = set_solution goal sol  in
                           FStar_Tactics_Monad.bind uu____2466
                             (fun uu____2472  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____2474 =
                                  let uu____2477 = bnorm_goal g  in
                                  FStar_Tactics_Monad.replace_cur uu____2477
                                   in
                                FStar_Tactics_Monad.bind uu____2474
                                  (fun uu____2479  ->
                                     FStar_Tactics_Monad.ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____2484 =
                 let uu____2486 = FStar_Tactics_Types.goal_env goal  in
                 let uu____2487 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____2486 uu____2487  in
               fail1 "goal is not an arrow (%s)" uu____2484)
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "intro") uu____2371
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder)
      FStar_Tactics_Monad.tac)
  =
  fun uu____2505  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2528 =
            let uu____2535 =
              let uu____2536 = FStar_Tactics_Types.goal_env goal  in
              let uu____2537 = FStar_Tactics_Types.goal_type goal  in
              whnf uu____2536 uu____2537  in
            FStar_Syntax_Util.arrow_one uu____2535  in
          match uu____2528 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____2550 =
                let uu____2552 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____2552  in
              if uu____2550
              then FStar_Tactics_Monad.fail "Codomain is effectful"
              else
                (let bv =
                   let uu____2569 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____2569
                    in
                 let bs =
                   let uu____2580 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2580; b]  in
                 let env' =
                   let uu____2606 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____2606 bs  in
                 let uu____2607 =
                   FStar_Tactics_Monad.new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 FStar_Tactics_Monad.bind uu____2607
                   (fun uu____2633  ->
                      match uu____2633 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____2647 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____2650 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____2647
                              FStar_Parser_Const.effect_Tot_lid uu____2650 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____2668 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____2668 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____2690 =
                                   let uu____2691 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____2691.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____2690
                                  in
                               let uu____2707 = set_solution goal tm  in
                               FStar_Tactics_Monad.bind uu____2707
                                 (fun uu____2716  ->
                                    let uu____2717 =
                                      let uu____2720 =
                                        bnorm_goal
                                          (let uu___446_2723 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___446_2723.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___446_2723.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___446_2723.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___446_2723.FStar_Tactics_Types.label)
                                           })
                                         in
                                      FStar_Tactics_Monad.replace_cur
                                        uu____2720
                                       in
                                    FStar_Tactics_Monad.bind uu____2717
                                      (fun uu____2730  ->
                                         let uu____2731 =
                                           let uu____2736 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____2736, b)  in
                                         FStar_Tactics_Monad.ret uu____2731)))))
          | FStar_Pervasives_Native.None  ->
              let uu____2745 =
                let uu____2747 = FStar_Tactics_Types.goal_env goal  in
                let uu____2748 = FStar_Tactics_Types.goal_type goal  in
                tts uu____2747 uu____2748  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2745))
  
let (norm :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    unit FStar_Tactics_Monad.tac)
  =
  fun s  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal  ->
         FStar_Tactics_Monad.mlog
           (fun uu____2772  ->
              let uu____2773 =
                let uu____2775 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____2775  in
              FStar_Util.print1 "norm: witness = %s\n" uu____2773)
           (fun uu____2781  ->
              let steps =
                let uu____2785 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____2785
                 in
              let t =
                let uu____2789 = FStar_Tactics_Types.goal_env goal  in
                let uu____2790 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____2789 uu____2790  in
              let uu____2791 = FStar_Tactics_Types.goal_with_type goal t  in
              FStar_Tactics_Monad.replace_cur uu____2791))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2816 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____2824 -> g.FStar_Tactics_Types.opts
                 | uu____2827 -> FStar_Options.peek ()  in
               FStar_Tactics_Monad.mlog
                 (fun uu____2832  ->
                    let uu____2833 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____2833)
                 (fun uu____2838  ->
                    let uu____2839 = __tc_lax e t  in
                    FStar_Tactics_Monad.bind uu____2839
                      (fun uu____2860  ->
                         match uu____2860 with
                         | (t1,uu____2870,uu____2871) ->
                             let steps =
                               let uu____2875 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____2875
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             FStar_Tactics_Monad.mlog
                               (fun uu____2881  ->
                                  let uu____2882 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____2882)
                               (fun uu____2886  -> FStar_Tactics_Monad.ret t2))))
           in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_term")
          uu____2816
  
let (refine_intro : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____2899  ->
    let uu____2902 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g  ->
           let uu____2909 =
             let uu____2920 = FStar_Tactics_Types.goal_env g  in
             let uu____2921 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____2920 uu____2921
              in
           match uu____2909 with
           | (uu____2924,FStar_Pervasives_Native.None ) ->
               FStar_Tactics_Monad.fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____2950 =
                 let uu____2955 =
                   let uu____2960 =
                     let uu____2961 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____2961]  in
                   FStar_Syntax_Subst.open_term uu____2960 phi  in
                 match uu____2955 with
                 | (bvs,phi1) ->
                     let uu____2986 =
                       let uu____2987 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____2987  in
                     (uu____2986, phi1)
                  in
               (match uu____2950 with
                | (bv1,phi1) ->
                    let uu____3006 =
                      let uu____3009 = FStar_Tactics_Types.goal_env g  in
                      let uu____3010 =
                        let uu____3011 =
                          let uu____3014 =
                            let uu____3015 =
                              let uu____3022 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3022)  in
                            FStar_Syntax_Syntax.NT uu____3015  in
                          [uu____3014]  in
                        FStar_Syntax_Subst.subst uu____3011 phi1  in
                      FStar_Tactics_Monad.mk_irrelevant_goal
                        "refine_intro refinement" uu____3009 uu____3010
                        g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    FStar_Tactics_Monad.bind uu____3006
                      (fun g2  ->
                         FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                           (fun uu____3031  ->
                              FStar_Tactics_Monad.add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "refine_intro")
      uu____2902
  
let (__exact_now :
  Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun set_expected_typ1  ->
    fun t  ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3060 = FStar_Tactics_Types.goal_env goal  in
               let uu____3061 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3060 uu____3061
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3064 = __tc env t  in
           FStar_Tactics_Monad.bind uu____3064
             (fun uu____3083  ->
                match uu____3083 with
                | (t1,typ,guard) ->
                    FStar_Tactics_Monad.mlog
                      (fun uu____3098  ->
                         let uu____3099 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3101 =
                           let uu____3103 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3103
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3099 uu____3101)
                      (fun uu____3107  ->
                         let uu____3108 =
                           let uu____3111 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3111 guard  in
                         FStar_Tactics_Monad.bind uu____3108
                           (fun uu____3114  ->
                              FStar_Tactics_Monad.mlog
                                (fun uu____3118  ->
                                   let uu____3119 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3121 =
                                     let uu____3123 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3123
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3119 uu____3121)
                                (fun uu____3127  ->
                                   let uu____3128 =
                                     let uu____3132 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3133 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3132 typ uu____3133  in
                                   FStar_Tactics_Monad.bind uu____3128
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3143 =
                                             let uu____3150 =
                                               let uu____3156 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal
                                                  in
                                               tts uu____3156  in
                                             let uu____3157 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu____3150 typ uu____3157
                                              in
                                           match uu____3143 with
                                           | (typ1,goalt) ->
                                               let uu____3166 =
                                                 let uu____3168 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 tts uu____3168 t1  in
                                               let uu____3169 =
                                                 let uu____3171 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____3172 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal
                                                    in
                                                 tts uu____3171 uu____3172
                                                  in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu____3166 typ1 goalt
                                                 uu____3169)))))))
  
let (t_exact :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3198 =
          FStar_Tactics_Monad.mlog
            (fun uu____3203  ->
               let uu____3204 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3204)
            (fun uu____3209  ->
               let uu____3210 =
                 let uu____3217 = __exact_now set_expected_typ1 tm  in
                 catch uu____3217  in
               FStar_Tactics_Monad.bind uu____3210
                 (fun uu___2_3226  ->
                    match uu___2_3226 with
                    | FStar_Util.Inr r -> FStar_Tactics_Monad.ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        FStar_Tactics_Monad.traise e
                    | FStar_Util.Inl e ->
                        FStar_Tactics_Monad.mlog
                          (fun uu____3237  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3241  ->
                             let uu____3242 =
                               let uu____3249 =
                                 let uu____3252 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 FStar_Tactics_Monad.bind uu____3252
                                   (fun uu____3257  ->
                                      let uu____3258 = refine_intro ()  in
                                      FStar_Tactics_Monad.bind uu____3258
                                        (fun uu____3262  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____3249  in
                             FStar_Tactics_Monad.bind uu____3242
                               (fun uu___1_3269  ->
                                  match uu___1_3269 with
                                  | FStar_Util.Inr r ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3278  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____3281  ->
                                           FStar_Tactics_Monad.ret ())
                                  | FStar_Util.Inl uu____3282 ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3284  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____3287  ->
                                           FStar_Tactics_Monad.traise e)))))
           in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "exact") uu____3198
  
let rec (__try_unify_by_application :
  Prims.bool ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
              FStar_Syntax_Syntax.ctx_uvar) Prims.list
              FStar_Tactics_Monad.tac)
  =
  fun only_match  ->
    fun acc  ->
      fun e  ->
        fun ty1  ->
          fun ty2  ->
            let f = if only_match then do_match else do_unify  in
            let uu____3388 = f e ty2 ty1  in
            FStar_Tactics_Monad.bind uu____3388
              (fun uu___3_3402  ->
                 if uu___3_3402
                 then FStar_Tactics_Monad.ret acc
                 else
                   (let uu____3422 = FStar_Syntax_Util.arrow_one ty1  in
                    match uu____3422 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____3443 = term_to_string e ty1  in
                        let uu____3445 = term_to_string e ty2  in
                        fail2 "Could not instantiate, %s to %s" uu____3443
                          uu____3445
                    | FStar_Pervasives_Native.Some (b,c) ->
                        let uu____3462 =
                          let uu____3464 = FStar_Syntax_Util.is_total_comp c
                             in
                          Prims.op_Negation uu____3464  in
                        if uu____3462
                        then FStar_Tactics_Monad.fail "Codomain is effectful"
                        else
                          (let uu____3488 =
                             FStar_Tactics_Monad.new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           FStar_Tactics_Monad.bind uu____3488
                             (fun uu____3515  ->
                                match uu____3515 with
                                | (uvt,uv) ->
                                    let typ = FStar_Syntax_Util.comp_result c
                                       in
                                    let typ' =
                                      FStar_Syntax_Subst.subst
                                        [FStar_Syntax_Syntax.NT
                                           ((FStar_Pervasives_Native.fst b),
                                             uvt)] typ
                                       in
                                    __try_unify_by_application only_match
                                      ((uvt, (FStar_Pervasives_Native.snd b),
                                         uv) :: acc) e typ' ty2))))
  
let (try_unify_by_application :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
            FStar_Syntax_Syntax.ctx_uvar) Prims.list FStar_Tactics_Monad.tac)
  =
  fun only_match  ->
    fun e  ->
      fun ty1  ->
        fun ty2  -> __try_unify_by_application only_match [] e ty1 ty2
  
let (t_apply :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun uopt  ->
    fun only_match  ->
      fun tm  ->
        let uu____3621 =
          FStar_Tactics_Monad.mlog
            (fun uu____3626  ->
               let uu____3627 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____3627)
            (fun uu____3631  ->
               FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                 (fun goal  ->
                    let e = FStar_Tactics_Types.goal_env goal  in
                    let uu____3637 = __tc e tm  in
                    FStar_Tactics_Monad.bind uu____3637
                      (fun uu____3658  ->
                         match uu____3658 with
                         | (tm1,typ,guard) ->
                             let typ1 = bnorm e typ  in
                             let uu____3671 =
                               let uu____3682 =
                                 FStar_Tactics_Types.goal_type goal  in
                               try_unify_by_application only_match e typ1
                                 uu____3682
                                in
                             FStar_Tactics_Monad.bind uu____3671
                               (fun uvs  ->
                                  FStar_Tactics_Monad.mlog
                                    (fun uu____3703  ->
                                       let uu____3704 =
                                         FStar_Common.string_of_list
                                           (fun uu____3716  ->
                                              match uu____3716 with
                                              | (t,uu____3725,uu____3726) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t) uvs
                                          in
                                       FStar_Util.print1
                                         "t_apply: found args = %s\n"
                                         uu____3704)
                                    (fun uu____3734  ->
                                       let fix_qual q =
                                         match q with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Meta
                                             uu____3749) ->
                                             FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                                  false)
                                         | uu____3753 -> q  in
                                       let w =
                                         FStar_List.fold_right
                                           (fun uu____3776  ->
                                              fun w  ->
                                                match uu____3776 with
                                                | (uvt,q,uu____3794) ->
                                                    FStar_Syntax_Util.mk_app
                                                      w [(uvt, (fix_qual q))])
                                           uvs tm1
                                          in
                                       let uvset =
                                         let uu____3826 =
                                           FStar_Syntax_Free.new_uv_set ()
                                            in
                                         FStar_List.fold_right
                                           (fun uu____3843  ->
                                              fun s  ->
                                                match uu____3843 with
                                                | (uu____3855,uu____3856,uv)
                                                    ->
                                                    let uu____3858 =
                                                      FStar_Syntax_Free.uvars
                                                        uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                       in
                                                    FStar_Util.set_union s
                                                      uu____3858) uvs
                                           uu____3826
                                          in
                                       let free_in_some_goal uv =
                                         FStar_Util.set_mem uv uvset  in
                                       let uu____3868 = solve' goal w  in
                                       FStar_Tactics_Monad.bind uu____3868
                                         (fun uu____3873  ->
                                            let uu____3874 =
                                              FStar_Tactics_Monad.mapM
                                                (fun uu____3891  ->
                                                   match uu____3891 with
                                                   | (uvt,q,uv) ->
                                                       let uu____3903 =
                                                         FStar_Syntax_Unionfind.find
                                                           uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                          in
                                                       (match uu____3903 with
                                                        | FStar_Pervasives_Native.Some
                                                            uu____3908 ->
                                                            FStar_Tactics_Monad.ret
                                                              ()
                                                        | FStar_Pervasives_Native.None
                                                             ->
                                                            let uu____3909 =
                                                              uopt &&
                                                                (free_in_some_goal
                                                                   uv)
                                                               in
                                                            if uu____3909
                                                            then
                                                              FStar_Tactics_Monad.ret
                                                                ()
                                                            else
                                                              (let uu____3916
                                                                 =
                                                                 let uu____3919
                                                                   =
                                                                   bnorm_goal
                                                                    (let uu___606_3922
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___606_3922.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___606_3922.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___606_3922.FStar_Tactics_Types.label)
                                                                    })
                                                                    in
                                                                 [uu____3919]
                                                                  in
                                                               FStar_Tactics_Monad.add_goals
                                                                 uu____3916)))
                                                uvs
                                               in
                                            FStar_Tactics_Monad.bind
                                              uu____3874
                                              (fun uu____3927  ->
                                                 proc_guard "apply guard" e
                                                   guard)))))))
           in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply") uu____3621
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____3955 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____3955
    then
      let uu____3964 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3979 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4032 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3964 with
      | (pre,post) ->
          let post1 =
            let uu____4065 =
              let uu____4076 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4076]  in
            FStar_Syntax_Util.mk_app post uu____4065  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4107 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4107
       then
         let uu____4116 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4116
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let rec fold_left :
  'a 'b .
    ('a -> 'b -> 'b FStar_Tactics_Monad.tac) ->
      'b -> 'a Prims.list -> 'b FStar_Tactics_Monad.tac
  =
  fun f  ->
    fun e  ->
      fun xs  ->
        match xs with
        | [] -> FStar_Tactics_Monad.ret e
        | x::xs1 ->
            let uu____4195 = f x e  in
            FStar_Tactics_Monad.bind uu____4195
              (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun tm  ->
    let uu____4210 =
      let uu____4213 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps  ->
             FStar_Tactics_Monad.mlog
               (fun uu____4220  ->
                  let uu____4221 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4221)
               (fun uu____4226  ->
                  let is_unit_t t =
                    let uu____4234 =
                      let uu____4235 = FStar_Syntax_Subst.compress t  in
                      uu____4235.FStar_Syntax_Syntax.n  in
                    match uu____4234 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4241 -> false  in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                    (fun goal  ->
                       let uu____4246 =
                         let uu____4255 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4255 tm  in
                       FStar_Tactics_Monad.bind uu____4246
                         (fun uu____4270  ->
                            match uu____4270 with
                            | (tm1,t,guard) ->
                                let uu____4282 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4282 with
                                 | (bs,comp) ->
                                     let uu____4291 = lemma_or_sq comp  in
                                     (match uu____4291 with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Tactics_Monad.fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4311 =
                                            fold_left
                                              (fun uu____4373  ->
                                                 fun uu____4374  ->
                                                   match (uu____4373,
                                                           uu____4374)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____4525 =
                                                         is_unit_t b_t  in
                                                       if uu____4525
                                                       then
                                                         FStar_All.pipe_left
                                                           FStar_Tactics_Monad.ret
                                                           (((FStar_Syntax_Util.exp_unit,
                                                               aq) :: uvs),
                                                             imps,
                                                             ((FStar_Syntax_Syntax.NT
                                                                 (b,
                                                                   FStar_Syntax_Util.exp_unit))
                                                             :: subst1))
                                                       else
                                                         (let uu____4648 =
                                                            let uu____4655 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_Tactics_Monad.new_uvar
                                                              "apply_lemma"
                                                              uu____4655 b_t
                                                             in
                                                          FStar_Tactics_Monad.bind
                                                            uu____4648
                                                            (fun uu____4686 
                                                               ->
                                                               match uu____4686
                                                               with
                                                               | (t1,u) ->
                                                                   FStar_All.pipe_left
                                                                    FStar_Tactics_Monad.ret
                                                                    (((t1,
                                                                    aq) ::
                                                                    uvs),
                                                                    ((t1, u)
                                                                    :: imps),
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b, t1))
                                                                    ::
                                                                    subst1)))))
                                              ([], [], []) bs
                                             in
                                          FStar_Tactics_Monad.bind uu____4311
                                            (fun uu____4872  ->
                                               match uu____4872 with
                                               | (uvs,implicits,subst1) ->
                                                   let implicits1 =
                                                     FStar_List.rev implicits
                                                      in
                                                   let uvs1 =
                                                     FStar_List.rev uvs  in
                                                   let pre1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1 pre
                                                      in
                                                   let post1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1 post
                                                      in
                                                   let uu____4960 =
                                                     let uu____4964 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____4965 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____4966 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____4964
                                                       uu____4965 uu____4966
                                                      in
                                                   FStar_Tactics_Monad.bind
                                                     uu____4960
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____4978 =
                                                            let uu____4985 =
                                                              let uu____4991
                                                                =
                                                                FStar_Tactics_Types.goal_env
                                                                  goal
                                                                 in
                                                              tts uu____4991
                                                               in
                                                            let uu____4992 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            let uu____4993 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Err.print_discrepancy
                                                              uu____4985
                                                              uu____4992
                                                              uu____4993
                                                             in
                                                          match uu____4978
                                                          with
                                                          | (post2,goalt) ->
                                                              let uu____5002
                                                                =
                                                                let uu____5004
                                                                  =
                                                                  FStar_Tactics_Types.goal_env
                                                                    goal
                                                                   in
                                                                tts
                                                                  uu____5004
                                                                  tm1
                                                                 in
                                                              fail3
                                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                uu____5002
                                                                post2 goalt
                                                        else
                                                          (let uu____5008 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           FStar_Tactics_Monad.bind
                                                             uu____5008
                                                             (fun uu____5016 
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____5042
                                                                    =
                                                                    let uu____5045
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5045
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5042
                                                                     in
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun u  ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars
                                                                   in
                                                                let appears
                                                                  uv goals =
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun g' 
                                                                    ->
                                                                    let uu____5081
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5081)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____5098
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____5098
                                                                  with
                                                                  | (hd1,uu____5117)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5144)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5161
                                                                    -> false)
                                                                   in
                                                                let uu____5163
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    implicits1
                                                                    (
                                                                    FStar_Tactics_Monad.mapM
                                                                    (fun imp 
                                                                    ->
                                                                    let uu____5204
                                                                    = imp  in
                                                                    match uu____5204
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____5215
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5215
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5237)
                                                                    ->
                                                                    let uu____5262
                                                                    =
                                                                    let uu____5263
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5263.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5262
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5271)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___723_5291
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___723_5291.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___723_5291.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___723_5291.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___723_5291.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    FStar_Tactics_Monad.ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5294
                                                                    ->
                                                                    FStar_Tactics_Monad.mlog
                                                                    (fun
                                                                    uu____5300
                                                                     ->
                                                                    let uu____5301
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5303
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5301
                                                                    uu____5303)
                                                                    (fun
                                                                    uu____5309
                                                                     ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____5311
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true
                                                                    uu____5311
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5313
                                                                    =
                                                                    let uu____5316
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5320
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5322
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5320
                                                                    uu____5322
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5328
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5316
                                                                    uu____5328
                                                                    g_typ  in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5313
                                                                    (fun
                                                                    uu____5332
                                                                     ->
                                                                    FStar_Tactics_Monad.ret
                                                                    []))))))
                                                                   in
                                                                FStar_Tactics_Monad.bind
                                                                  uu____5163
                                                                  (fun
                                                                    sub_goals
                                                                     ->
                                                                    let sub_goals1
                                                                    =
                                                                    FStar_List.flatten
                                                                    sub_goals
                                                                     in
                                                                    let rec filter'
                                                                    f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____5396
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5396
                                                                    then
                                                                    let uu____5401
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5401
                                                                    else
                                                                    filter' f
                                                                    xs1  in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____5416
                                                                    =
                                                                    let uu____5418
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5418
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5416)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5419
                                                                    =
                                                                    let uu____5422
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5422
                                                                    guard  in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5419
                                                                    (fun
                                                                    uu____5426
                                                                     ->
                                                                    let uu____5427
                                                                    =
                                                                    let uu____5430
                                                                    =
                                                                    let uu____5432
                                                                    =
                                                                    let uu____5434
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5435
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5434
                                                                    uu____5435
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5432
                                                                     in
                                                                    if
                                                                    uu____5430
                                                                    then
                                                                    let uu____5439
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    FStar_Tactics_Monad.add_irrelevant_goal
                                                                    goal
                                                                    "apply_lemma precondition"
                                                                    uu____5439
                                                                    pre1
                                                                    else
                                                                    FStar_Tactics_Monad.ret
                                                                    ()  in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5427
                                                                    (fun
                                                                    uu____5444
                                                                     ->
                                                                    FStar_Tactics_Monad.add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____4213  in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply_lemma")
      uu____4210
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5468 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5468 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5478::(e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5538::uu____5539::(e1,uu____5541)::(e2,uu____5543)::[]))
        when FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5620 ->
        let uu____5623 = FStar_Syntax_Util.unb2t typ  in
        (match uu____5623 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____5637 = FStar_Syntax_Util.head_and_args t  in
             (match uu____5637 with
              | (hd1,args) ->
                  let uu____5686 =
                    let uu____5701 =
                      let uu____5702 = FStar_Syntax_Subst.compress hd1  in
                      uu____5702.FStar_Syntax_Syntax.n  in
                    (uu____5701, args)  in
                  (match uu____5686 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(uu____5722,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____5723))::
                      (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                           )::[])
                       when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____5791 -> FStar_Pervasives_Native.None)))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5828 = destruct_eq' typ  in
    match uu____5828 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5858 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5858 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar  ->
    fun e  ->
      let rec aux e1 =
        let uu____5927 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5927 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____5985 = aux e'  in
               FStar_Util.map_opt uu____5985
                 (fun uu____6016  ->
                    match uu____6016 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____6042 = aux e  in
      FStar_Util.map_opt uu____6042
        (fun uu____6073  ->
           match uu____6073 with
           | (e',bv,bvs) -> (e', bv, (FStar_List.rev bvs)))
  
let (push_bvs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env)
  =
  fun e  ->
    fun bvs  ->
      FStar_List.fold_left
        (fun e1  -> fun b  -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
  
let (subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Tactics_Types.goal ->
        (FStar_Syntax_Syntax.bv * FStar_Tactics_Types.goal)
          FStar_Pervasives_Native.option FStar_Tactics_Monad.tac)
  =
  fun b1  ->
    fun b2  ->
      fun g  ->
        let uu____6150 =
          let uu____6161 = FStar_Tactics_Types.goal_env g  in
          split_env b1 uu____6161  in
        match uu____6150 with
        | FStar_Pervasives_Native.Some (e0,b11,bvs) ->
            let bs =
              FStar_List.map FStar_Syntax_Syntax.mk_binder (b11 :: bvs)  in
            let t = FStar_Tactics_Types.goal_type g  in
            let uu____6201 =
              let uu____6214 = FStar_Syntax_Subst.close_binders bs  in
              let uu____6223 = FStar_Syntax_Subst.close bs t  in
              (uu____6214, uu____6223)  in
            (match uu____6201 with
             | (bs',t') ->
                 let bs'1 =
                   let uu____6267 = FStar_Syntax_Syntax.mk_binder b2  in
                   let uu____6274 = FStar_List.tail bs'  in uu____6267 ::
                     uu____6274
                    in
                 let uu____6295 = FStar_Syntax_Subst.open_term bs'1 t'  in
                 (match uu____6295 with
                  | (bs'',t'') ->
                      let b21 =
                        let uu____6311 = FStar_List.hd bs''  in
                        FStar_Pervasives_Native.fst uu____6311  in
                      let new_env =
                        let uu____6327 =
                          FStar_List.map FStar_Pervasives_Native.fst bs''  in
                        push_bvs e0 uu____6327  in
                      let uu____6338 =
                        FStar_Tactics_Monad.new_uvar "subst_goal" new_env t''
                         in
                      FStar_Tactics_Monad.bind uu____6338
                        (fun uu____6362  ->
                           match uu____6362 with
                           | (uvt,uv) ->
                               let goal' =
                                 FStar_Tactics_Types.mk_goal new_env uv
                                   g.FStar_Tactics_Types.opts
                                   g.FStar_Tactics_Types.is_guard
                                   g.FStar_Tactics_Types.label
                                  in
                               let sol =
                                 let uu____6381 =
                                   FStar_Syntax_Util.abs bs'' uvt
                                     FStar_Pervasives_Native.None
                                    in
                                 let uu____6384 =
                                   FStar_List.map
                                     (fun uu____6405  ->
                                        match uu____6405 with
                                        | (bv,q) ->
                                            let uu____6418 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                bv
                                               in
                                            FStar_Syntax_Syntax.as_arg
                                              uu____6418) bs
                                    in
                                 FStar_Syntax_Util.mk_app uu____6381
                                   uu____6384
                                  in
                               let uu____6419 = set_solution g sol  in
                               FStar_Tactics_Monad.bind uu____6419
                                 (fun uu____6429  ->
                                    FStar_Tactics_Monad.ret
                                      (FStar_Pervasives_Native.Some
                                         (b21, goal'))))))
        | FStar_Pervasives_Native.None  ->
            FStar_Tactics_Monad.ret FStar_Pervasives_Native.None
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun h  ->
    let uu____6468 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal  ->
           let uu____6476 = h  in
           match uu____6476 with
           | (bv,uu____6480) ->
               FStar_Tactics_Monad.mlog
                 (fun uu____6488  ->
                    let uu____6489 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____6491 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6489
                      uu____6491)
                 (fun uu____6496  ->
                    let uu____6497 =
                      let uu____6508 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____6508  in
                    match uu____6497 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Tactics_Monad.fail
                          "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____6535 =
                          let uu____6542 =
                            whnf e0 bv1.FStar_Syntax_Syntax.sort  in
                          destruct_eq uu____6542  in
                        (match uu____6535 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6551 =
                               let uu____6552 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6552.FStar_Syntax_Syntax.n  in
                             (match uu____6551 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let t = FStar_Tactics_Types.goal_type goal
                                     in
                                  let bs =
                                    FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder bvs
                                     in
                                  let uu____6579 =
                                    let uu____6584 =
                                      FStar_Syntax_Subst.close_binders bs  in
                                    let uu____6585 =
                                      FStar_Syntax_Subst.close bs t  in
                                    (uu____6584, uu____6585)  in
                                  (match uu____6579 with
                                   | (bs',t') ->
                                       let uu____6590 =
                                         let uu____6595 =
                                           FStar_Syntax_Subst.subst_binders s
                                             bs'
                                            in
                                         let uu____6596 =
                                           FStar_Syntax_Subst.subst s t  in
                                         (uu____6595, uu____6596)  in
                                       (match uu____6590 with
                                        | (bs'1,t'1) ->
                                            let uu____6601 =
                                              FStar_Syntax_Subst.open_term
                                                bs'1 t'1
                                               in
                                            (match uu____6601 with
                                             | (bs'',t'') ->
                                                 let new_env =
                                                   let uu____6611 =
                                                     let uu____6614 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         bs''
                                                        in
                                                     bv1 :: uu____6614  in
                                                   push_bvs e0 uu____6611  in
                                                 let uu____6625 =
                                                   FStar_Tactics_Monad.new_uvar
                                                     "rewrite" new_env t''
                                                    in
                                                 FStar_Tactics_Monad.bind
                                                   uu____6625
                                                   (fun uu____6643  ->
                                                      match uu____6643 with
                                                      | (uvt,uv) ->
                                                          let goal' =
                                                            FStar_Tactics_Types.mk_goal
                                                              new_env uv
                                                              goal.FStar_Tactics_Types.opts
                                                              goal.FStar_Tactics_Types.is_guard
                                                              goal.FStar_Tactics_Types.label
                                                             in
                                                          let sol =
                                                            let uu____6656 =
                                                              FStar_Syntax_Util.abs
                                                                bs'' uvt
                                                                FStar_Pervasives_Native.None
                                                               in
                                                            let uu____6659 =
                                                              FStar_List.map
                                                                (fun
                                                                   uu____6680
                                                                    ->
                                                                   match uu____6680
                                                                   with
                                                                   | 
                                                                   (bv2,uu____6688)
                                                                    ->
                                                                    let uu____6693
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv2  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____6693)
                                                                bs
                                                               in
                                                            FStar_Syntax_Util.mk_app
                                                              uu____6656
                                                              uu____6659
                                                             in
                                                          let uu____6694 =
                                                            set_solution goal
                                                              sol
                                                             in
                                                          FStar_Tactics_Monad.bind
                                                            uu____6694
                                                            (fun uu____6698 
                                                               ->
                                                               FStar_Tactics_Monad.replace_cur
                                                                 goal')))))
                              | uu____6699 ->
                                  FStar_Tactics_Monad.fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6701 ->
                             FStar_Tactics_Monad.fail
                               "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rewrite") uu____6468
  
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac)
  =
  fun b  ->
    fun s  ->
      let uu____6731 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal  ->
             let uu____6753 = b  in
             match uu____6753 with
             | (bv,q) ->
                 let bv' =
                   let uu____6769 =
                     let uu___901_6770 = bv  in
                     let uu____6771 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6771;
                       FStar_Syntax_Syntax.index =
                         (uu___901_6770.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___901_6770.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6769  in
                 let uu____6773 = subst_goal bv bv' goal  in
                 FStar_Tactics_Monad.bind uu____6773
                   (fun uu___4_6795  ->
                      match uu___4_6795 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Tactics_Monad.fail
                            "binder not found in environment"
                      | FStar_Pervasives_Native.Some (bv'1,goal1) ->
                          let uu____6827 =
                            FStar_Tactics_Monad.replace_cur goal1  in
                          FStar_Tactics_Monad.bind uu____6827
                            (fun uu____6837  ->
                               FStar_Tactics_Monad.ret (bv'1, q))))
         in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rename_to")
        uu____6731
  
let (binder_retype :
  FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b  ->
    let uu____6873 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal  ->
           let uu____6882 = b  in
           match uu____6882 with
           | (bv,uu____6886) ->
               let uu____6891 =
                 let uu____6902 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6902  in
               (match uu____6891 with
                | FStar_Pervasives_Native.None  ->
                    FStar_Tactics_Monad.fail
                      "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____6929 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6929 with
                     | (ty,u) ->
                         let uu____6938 =
                           FStar_Tactics_Monad.new_uvar "binder_retype" e0 ty
                            in
                         FStar_Tactics_Monad.bind uu____6938
                           (fun uu____6957  ->
                              match uu____6957 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___928_6967 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___928_6967.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___928_6967.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6971 =
                                      let uu____6972 =
                                        let uu____6979 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____6979)  in
                                      FStar_Syntax_Syntax.NT uu____6972  in
                                    [uu____6971]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___933_6991 = b1  in
                                         let uu____6992 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___933_6991.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___933_6991.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6992
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  FStar_Tactics_Monad.bind
                                    FStar_Tactics_Monad.dismiss
                                    (fun uu____6999  ->
                                       let new_goal =
                                         let uu____7001 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____7002 =
                                           let uu____7003 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____7003
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____7001 uu____7002
                                          in
                                       let uu____7004 =
                                         FStar_Tactics_Monad.add_goals
                                           [new_goal]
                                          in
                                       FStar_Tactics_Monad.bind uu____7004
                                         (fun uu____7009  ->
                                            let uu____7010 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            FStar_Tactics_Monad.add_irrelevant_goal
                                              goal "binder_retype equation"
                                              e0 uu____7010))))))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "binder_retype")
      uu____6873
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac)
  =
  fun s  ->
    fun b  ->
      let uu____7036 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal  ->
             let uu____7045 = b  in
             match uu____7045 with
             | (bv,uu____7049) ->
                 let uu____7054 =
                   let uu____7065 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____7065  in
                 (match uu____7054 with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Tactics_Monad.fail
                        "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____7095 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____7095
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___954_7100 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___954_7100.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___954_7100.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____7102 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      FStar_Tactics_Monad.replace_cur uu____7102))
         in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_binder_type")
        uu____7036
  
let (revert : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7115  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal  ->
         let uu____7121 =
           let uu____7128 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____7128  in
         match uu____7121 with
         | FStar_Pervasives_Native.None  ->
             FStar_Tactics_Monad.fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____7145 =
                 let uu____7148 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____7148  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____7145
                in
             let uu____7163 = FStar_Tactics_Monad.new_uvar "revert" env' typ'
                in
             FStar_Tactics_Monad.bind uu____7163
               (fun uu____7179  ->
                  match uu____7179 with
                  | (r,u_r) ->
                      let uu____7188 =
                        let uu____7191 =
                          let uu____7192 =
                            let uu____7193 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____7193.FStar_Syntax_Syntax.pos  in
                          let uu____7196 =
                            let uu____7201 =
                              let uu____7202 =
                                let uu____7211 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____7211  in
                              [uu____7202]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____7201  in
                          uu____7196 FStar_Pervasives_Native.None uu____7192
                           in
                        set_solution goal uu____7191  in
                      FStar_Tactics_Monad.bind uu____7188
                        (fun uu____7230  ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                               goal.FStar_Tactics_Types.label
                              in
                           FStar_Tactics_Monad.replace_cur g)))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____7244 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____7244
  
let (clear : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal  ->
         FStar_Tactics_Monad.mlog
           (fun uu____7265  ->
              let uu____7266 = FStar_Syntax_Print.binder_to_string b  in
              let uu____7268 =
                let uu____7270 =
                  let uu____7272 =
                    let uu____7281 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____7281  in
                  FStar_All.pipe_right uu____7272 FStar_List.length  in
                FStar_All.pipe_right uu____7270 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____7266 uu____7268)
           (fun uu____7302  ->
              let uu____7303 =
                let uu____7314 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____7314  in
              match uu____7303 with
              | FStar_Pervasives_Native.None  ->
                  FStar_Tactics_Monad.fail
                    "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> FStar_Tactics_Monad.ret ()
                    | bv'::bvs2 ->
                        let uu____7359 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____7359
                        then
                          let uu____7364 =
                            let uu____7366 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____7366
                             in
                          FStar_Tactics_Monad.fail uu____7364
                        else check1 bvs2
                     in
                  let uu____7371 =
                    let uu____7373 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____7373  in
                  if uu____7371
                  then
                    FStar_Tactics_Monad.fail
                      "Cannot clear; binder present in goal"
                  else
                    (let uu____7380 = check1 bvs  in
                     FStar_Tactics_Monad.bind uu____7380
                       (fun uu____7386  ->
                          let env' = push_bvs e' bvs  in
                          let uu____7388 =
                            let uu____7395 =
                              FStar_Tactics_Types.goal_type goal  in
                            FStar_Tactics_Monad.new_uvar "clear.witness" env'
                              uu____7395
                             in
                          FStar_Tactics_Monad.bind uu____7388
                            (fun uu____7405  ->
                               match uu____7405 with
                               | (ut,uvar_ut) ->
                                   let uu____7414 = set_solution goal ut  in
                                   FStar_Tactics_Monad.bind uu____7414
                                     (fun uu____7419  ->
                                        let uu____7420 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        FStar_Tactics_Monad.replace_cur
                                          uu____7420))))))
  
let (clear_top : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7428  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal  ->
         let uu____7434 =
           let uu____7441 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____7441  in
         match uu____7434 with
         | FStar_Pervasives_Native.None  ->
             FStar_Tactics_Monad.fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____7450) ->
             let uu____7455 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____7455)
  
let (prune : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____7475 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____7475  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         FStar_Tactics_Monad.replace_cur g')
  
let (addns : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____7496 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____7496  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         FStar_Tactics_Monad.replace_cur g')
  
let (_trefl :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun l  ->
    fun r  ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g  ->
           let uu____7516 =
             let uu____7520 = FStar_Tactics_Types.goal_env g  in
             do_unify uu____7520 l r  in
           FStar_Tactics_Monad.bind uu____7516
             (fun b  ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____7531 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7531 l
                      in
                   let r1 =
                     let uu____7533 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7533 r
                      in
                   let uu____7534 =
                     let uu____7538 = FStar_Tactics_Types.goal_env g  in
                     do_unify uu____7538 l1 r1  in
                   FStar_Tactics_Monad.bind uu____7534
                     (fun b1  ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____7548 =
                             let uu____7555 =
                               let uu____7561 =
                                 FStar_Tactics_Types.goal_env g  in
                               tts uu____7561  in
                             FStar_TypeChecker_Err.print_discrepancy
                               uu____7555 l1 r1
                              in
                           match uu____7548 with
                           | (ls,rs) ->
                               fail2 "not a trivial equality ((%s) vs (%s))"
                                 ls rs)))))
  
let (trefl : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7578  ->
    let uu____7581 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g  ->
           let uu____7589 =
             let uu____7596 =
               let uu____7597 = FStar_Tactics_Types.goal_env g  in
               let uu____7598 = FStar_Tactics_Types.goal_type g  in
               whnf uu____7597 uu____7598  in
             destruct_eq uu____7596  in
           match uu____7589 with
           | FStar_Pervasives_Native.Some (l,r) -> _trefl l r
           | FStar_Pervasives_Native.None  ->
               let uu____7611 =
                 let uu____7613 = FStar_Tactics_Types.goal_env g  in
                 let uu____7614 = FStar_Tactics_Types.goal_type g  in
                 tts uu____7613 uu____7614  in
               fail1 "not an equality (%s)" uu____7611)
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "trefl") uu____7581
  
let (dup : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7628  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g  ->
         let env = FStar_Tactics_Types.goal_env g  in
         let uu____7636 =
           let uu____7643 = FStar_Tactics_Types.goal_type g  in
           FStar_Tactics_Monad.new_uvar "dup" env uu____7643  in
         FStar_Tactics_Monad.bind uu____7636
           (fun uu____7653  ->
              match uu____7653 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1040_7663 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1040_7663.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1040_7663.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1040_7663.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1040_7663.FStar_Tactics_Types.label)
                    }  in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____7667  ->
                       let t_eq =
                         let uu____7669 =
                           let uu____7670 = FStar_Tactics_Types.goal_type g
                              in
                           env.FStar_TypeChecker_Env.universe_of env
                             uu____7670
                            in
                         let uu____7671 = FStar_Tactics_Types.goal_type g  in
                         let uu____7672 = FStar_Tactics_Types.goal_witness g
                            in
                         FStar_Syntax_Util.mk_eq2 uu____7669 uu____7671 u
                           uu____7672
                          in
                       let uu____7673 =
                         FStar_Tactics_Monad.add_irrelevant_goal g
                           "dup equation" env t_eq
                          in
                       FStar_Tactics_Monad.bind uu____7673
                         (fun uu____7679  ->
                            let uu____7680 =
                              FStar_Tactics_Monad.add_goals [g']  in
                            FStar_Tactics_Monad.bind uu____7680
                              (fun uu____7684  -> FStar_Tactics_Monad.ret ())))))
  
let longest_prefix :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list -> ('a Prims.list * 'a Prims.list * 'a Prims.list)
  =
  fun f  ->
    fun l1  ->
      fun l2  ->
        let rec aux acc l11 l21 =
          match (l11, l21) with
          | (x::xs,y::ys) ->
              let uu____7810 = f x y  in
              if uu____7810 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____7833 -> (acc, l11, l21)  in
        let uu____7848 = aux [] l1 l2  in
        match uu____7848 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal ->
      FStar_Tactics_Types.goal FStar_Tactics_Monad.tac)
  =
  fun g1  ->
    fun g2  ->
      let close_forall_no_univs1 bs f =
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               FStar_Syntax_Util.mk_forall_no_univ
                 (FStar_Pervasives_Native.fst b) f1) bs f
         in
      let uu____7954 = get_phi g1  in
      match uu____7954 with
      | FStar_Pervasives_Native.None  ->
          FStar_Tactics_Monad.fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____7961 = get_phi g2  in
          (match uu____7961 with
           | FStar_Pervasives_Native.None  ->
               FStar_Tactics_Monad.fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____7974 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____7974 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____8005 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____8005 phi1  in
                    let t2 =
                      let uu____8015 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____8015 phi2  in
                    let uu____8024 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    FStar_Tactics_Monad.bind uu____8024
                      (fun uu____8029  ->
                         let uu____8030 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         FStar_Tactics_Monad.bind uu____8030
                           (fun uu____8037  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1092_8042 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____8043 =
                                  FStar_Util.smap_create (Prims.of_int (100))
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1092_8042.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1092_8042.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1092_8042.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1092_8042.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____8043;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1092_8042.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1092_8042.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1092_8042.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1092_8042.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1092_8042.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1092_8042.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1092_8042.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1092_8042.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1092_8042.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1092_8042.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1092_8042.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1092_8042.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1092_8042.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1092_8042.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1092_8042.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1092_8042.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1092_8042.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1092_8042.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1092_8042.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1092_8042.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1092_8042.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1092_8042.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1092_8042.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1092_8042.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1092_8042.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1092_8042.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1092_8042.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1092_8042.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1092_8042.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1092_8042.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1092_8042.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1092_8042.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1092_8042.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1092_8042.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1092_8042.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1092_8042.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1092_8042.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1092_8042.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1092_8042.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1092_8042.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1092_8042.FStar_TypeChecker_Env.erasable_types_tab)
                                }  in
                              let uu____8047 =
                                FStar_Tactics_Monad.mk_irrelevant_goal
                                  "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              FStar_Tactics_Monad.bind uu____8047
                                (fun goal  ->
                                   FStar_Tactics_Monad.mlog
                                     (fun uu____8057  ->
                                        let uu____8058 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g1
                                           in
                                        let uu____8060 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g2
                                           in
                                        let uu____8062 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            goal
                                           in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____8058 uu____8060 uu____8062)
                                     (fun uu____8066  ->
                                        FStar_Tactics_Monad.ret goal))))))
  
let (join : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____8074  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____8090 =
               FStar_Tactics_Monad.set
                 (let uu___1107_8095 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1107_8095.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1107_8095.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1107_8095.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1107_8095.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1107_8095.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1107_8095.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1107_8095.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1107_8095.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1107_8095.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1107_8095.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1107_8095.FStar_Tactics_Types.local_state)
                  })
                in
             FStar_Tactics_Monad.bind uu____8090
               (fun uu____8098  ->
                  let uu____8099 = join_goals g1 g2  in
                  FStar_Tactics_Monad.bind uu____8099
                    (fun g12  -> FStar_Tactics_Monad.add_goals [g12]))
         | uu____8104 -> FStar_Tactics_Monad.fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s  ->
    let uu____8120 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g  ->
           FStar_Options.push ();
           (let uu____8133 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____8133);
           (let res = FStar_Options.set_options s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1118_8140 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1118_8140.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1118_8140.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1118_8140.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1118_8140.FStar_Tactics_Types.label)
                   }  in
                 FStar_Tactics_Monad.replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "set_options")
      uu____8120
  
let (top_env : unit -> env FStar_Tactics_Monad.tac) =
  fun uu____8157  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps  ->
         FStar_All.pipe_left FStar_Tactics_Monad.ret
           ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____8172  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g  ->
         let uu____8180 =
           (FStar_Options.lax ()) ||
             (let uu____8183 = FStar_Tactics_Types.goal_env g  in
              uu____8183.FStar_TypeChecker_Env.lax)
            in
         FStar_Tactics_Monad.ret uu____8180)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8200 =
        FStar_Tactics_Monad.mlog
          (fun uu____8205  ->
             let uu____8206 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____8206)
          (fun uu____8210  ->
             FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
               (fun goal  ->
                  let env =
                    let uu____8216 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____8216 ty  in
                  let uu____8217 = __tc_ghost env tm  in
                  FStar_Tactics_Monad.bind uu____8217
                    (fun uu____8236  ->
                       match uu____8236 with
                       | (tm1,typ,guard) ->
                           FStar_Tactics_Monad.mlog
                             (fun uu____8250  ->
                                let uu____8251 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____8251)
                             (fun uu____8255  ->
                                FStar_Tactics_Monad.mlog
                                  (fun uu____8258  ->
                                     let uu____8259 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____8259)
                                  (fun uu____8264  ->
                                     let uu____8265 =
                                       proc_guard "unquote" env guard  in
                                     FStar_Tactics_Monad.bind uu____8265
                                       (fun uu____8270  ->
                                          FStar_Tactics_Monad.ret tm1))))))
         in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unquote") uu____8200
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8295 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> FStar_Tactics_Monad.ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8301 =
              let uu____8308 =
                let uu____8309 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8309
                 in
              FStar_Tactics_Monad.new_uvar "uvar_env.2" env uu____8308  in
            FStar_Tactics_Monad.bind uu____8301
              (fun uu____8326  ->
                 match uu____8326 with
                 | (typ,uvar_typ) -> FStar_Tactics_Monad.ret typ)
         in
      FStar_Tactics_Monad.bind uu____8295
        (fun typ  ->
           let uu____8338 = FStar_Tactics_Monad.new_uvar "uvar_env" env typ
              in
           FStar_Tactics_Monad.bind uu____8338
             (fun uu____8353  ->
                match uu____8353 with
                | (t,uvar_t) -> FStar_Tactics_Monad.ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t  ->
    let uu____8372 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8391 -> g.FStar_Tactics_Types.opts
             | uu____8394 -> FStar_Options.peek ()  in
           let uu____8397 = FStar_Syntax_Util.head_and_args t  in
           match uu____8397 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____8417);
                FStar_Syntax_Syntax.pos = uu____8418;
                FStar_Syntax_Syntax.vars = uu____8419;_},uu____8420)
               ->
               let env1 =
                 let uu___1172_8462 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1172_8462.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1172_8462.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1172_8462.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1172_8462.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1172_8462.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1172_8462.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1172_8462.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1172_8462.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1172_8462.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1172_8462.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1172_8462.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1172_8462.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1172_8462.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1172_8462.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1172_8462.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1172_8462.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___1172_8462.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1172_8462.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1172_8462.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1172_8462.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1172_8462.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1172_8462.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1172_8462.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1172_8462.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1172_8462.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1172_8462.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1172_8462.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1172_8462.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1172_8462.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1172_8462.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1172_8462.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1172_8462.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1172_8462.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1172_8462.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1172_8462.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___1172_8462.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1172_8462.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1172_8462.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1172_8462.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1172_8462.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1172_8462.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1172_8462.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1172_8462.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1172_8462.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1172_8462.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1172_8462.FStar_TypeChecker_Env.erasable_types_tab)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____8466 =
                 let uu____8469 = bnorm_goal g  in [uu____8469]  in
               FStar_Tactics_Monad.add_goals uu____8466
           | uu____8470 -> FStar_Tactics_Monad.fail "not a uvar")
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unshelve") uu____8372
  
let (tac_and :
  Prims.bool FStar_Tactics_Monad.tac ->
    Prims.bool FStar_Tactics_Monad.tac -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun t1  ->
    fun t2  ->
      let comp =
        FStar_Tactics_Monad.bind t1
          (fun b  ->
             let uu____8532 = if b then t2 else FStar_Tactics_Monad.ret false
                in
             FStar_Tactics_Monad.bind uu____8532
               (fun b'  ->
                  if b'
                  then FStar_Tactics_Monad.ret b'
                  else FStar_Tactics_Monad.fail ""))
         in
      let uu____8558 = trytac comp  in
      FStar_Tactics_Monad.bind uu____8558
        (fun uu___5_8570  ->
           match uu___5_8570 with
           | FStar_Pervasives_Native.Some (true ) ->
               FStar_Tactics_Monad.ret true
           | FStar_Pervasives_Native.Some (false ) -> failwith "impossible"
           | FStar_Pervasives_Native.None  -> FStar_Tactics_Monad.ret false)
  
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e  ->
    fun t1  ->
      fun t2  ->
        let uu____8612 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps  ->
               let uu____8620 = __tc e t1  in
               FStar_Tactics_Monad.bind uu____8620
                 (fun uu____8641  ->
                    match uu____8641 with
                    | (t11,ty1,g1) ->
                        let uu____8654 = __tc e t2  in
                        FStar_Tactics_Monad.bind uu____8654
                          (fun uu____8675  ->
                             match uu____8675 with
                             | (t21,ty2,g2) ->
                                 let uu____8688 =
                                   proc_guard "unify_env g1" e g1  in
                                 FStar_Tactics_Monad.bind uu____8688
                                   (fun uu____8695  ->
                                      let uu____8696 =
                                        proc_guard "unify_env g2" e g2  in
                                      FStar_Tactics_Monad.bind uu____8696
                                        (fun uu____8704  ->
                                           let uu____8705 =
                                             do_unify e ty1 ty2  in
                                           let uu____8709 =
                                             do_unify e t11 t21  in
                                           tac_and uu____8705 uu____8709)))))
           in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unify_env")
          uu____8612
  
let (launch_process :
  Prims.string ->
    Prims.string Prims.list ->
      Prims.string -> Prims.string FStar_Tactics_Monad.tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____8757  ->
             let uu____8758 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8758
             then
               let s =
                 FStar_Util.run_process "tactic_launch" prog args
                   (FStar_Pervasives_Native.Some input)
                  in
               FStar_Tactics_Monad.ret s
             else
               FStar_Tactics_Monad.fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
  
let (fresh_bv_named :
  Prims.string ->
    FStar_Reflection_Data.typ ->
      FStar_Syntax_Syntax.bv FStar_Tactics_Monad.tac)
  =
  fun nm  ->
    fun t  ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
        (fun uu____8792  ->
           let uu____8793 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           FStar_Tactics_Monad.ret uu____8793)
  
let (change : FStar_Reflection_Data.typ -> unit FStar_Tactics_Monad.tac) =
  fun ty  ->
    let uu____8804 =
      FStar_Tactics_Monad.mlog
        (fun uu____8809  ->
           let uu____8810 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8810)
        (fun uu____8814  ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g  ->
                let uu____8818 =
                  let uu____8827 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____8827 ty  in
                FStar_Tactics_Monad.bind uu____8818
                  (fun uu____8839  ->
                     match uu____8839 with
                     | (ty1,uu____8849,guard) ->
                         let uu____8851 =
                           let uu____8854 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____8854 guard  in
                         FStar_Tactics_Monad.bind uu____8851
                           (fun uu____8858  ->
                              let uu____8859 =
                                let uu____8863 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____8864 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____8863 uu____8864 ty1  in
                              FStar_Tactics_Monad.bind uu____8859
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____8873 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     FStar_Tactics_Monad.replace_cur
                                       uu____8873
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____8880 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____8881 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____8880 uu____8881
                                         in
                                      let nty =
                                        let uu____8883 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____8883 ty1  in
                                      let uu____8884 =
                                        let uu____8888 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____8888 ng nty  in
                                      FStar_Tactics_Monad.bind uu____8884
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____8897 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             FStar_Tactics_Monad.replace_cur
                                               uu____8897
                                           else
                                             FStar_Tactics_Monad.fail
                                               "not convertible")))))))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "change") uu____8804
  
let failwhen :
  'a .
    Prims.bool ->
      Prims.string ->
        (unit -> 'a FStar_Tactics_Monad.tac) -> 'a FStar_Tactics_Monad.tac
  =
  fun b  ->
    fun msg  -> fun k  -> if b then FStar_Tactics_Monad.fail msg else k ()
  
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list
      FStar_Tactics_Monad.tac)
  =
  fun s_tm  ->
    let uu____8971 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g  ->
           let uu____8989 =
             let uu____8998 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8998 s_tm  in
           FStar_Tactics_Monad.bind uu____8989
             (fun uu____9016  ->
                match uu____9016 with
                | (s_tm1,s_ty,guard) ->
                    let uu____9034 =
                      let uu____9037 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____9037 guard  in
                    FStar_Tactics_Monad.bind uu____9034
                      (fun uu____9051  ->
                         let s_ty1 =
                           let uu____9053 = FStar_Tactics_Types.goal_env g
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant] uu____9053
                             s_ty
                            in
                         let uu____9054 =
                           FStar_Syntax_Util.head_and_args' s_ty1  in
                         match uu____9054 with
                         | (h,args) ->
                             let uu____9099 =
                               let uu____9106 =
                                 let uu____9107 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____9107.FStar_Syntax_Syntax.n  in
                               match uu____9106 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   FStar_Tactics_Monad.ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____9122;
                                      FStar_Syntax_Syntax.vars = uu____9123;_},us)
                                   -> FStar_Tactics_Monad.ret (fv, us)
                               | uu____9133 ->
                                   FStar_Tactics_Monad.fail
                                     "type is not an fv"
                                in
                             FStar_Tactics_Monad.bind uu____9099
                               (fun uu____9154  ->
                                  match uu____9154 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____9170 =
                                        let uu____9173 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____9173 t_lid
                                         in
                                      (match uu____9170 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Tactics_Monad.fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid,t_us,t_ps,t_ty,mut,c_lids)
                                                ->
                                                let erasable =
                                                  FStar_Syntax_Util.has_attribute
                                                    se.FStar_Syntax_Syntax.sigattrs
                                                    FStar_Parser_Const.erasable_attr
                                                   in
                                                let uu____9214 =
                                                  erasable &&
                                                    (let uu____9217 =
                                                       is_irrelevant g  in
                                                     Prims.op_Negation
                                                       uu____9217)
                                                   in
                                                failwhen uu____9214
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____9227  ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____9240  ->
                                                          let uu____9241 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty
                                                             in
                                                          match uu____9241
                                                          with
                                                          | (t_ps1,t_ty1) ->
                                                              let uu____9256
                                                                =
                                                                FStar_Tactics_Monad.mapM
                                                                  (fun c_lid 
                                                                    ->
                                                                    let uu____9284
                                                                    =
                                                                    let uu____9287
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____9287
                                                                    c_lid  in
                                                                    match uu____9284
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "ctor not found?"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (match 
                                                                    se1.FStar_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Sig_datacon
                                                                    (_c_lid,c_us,c_ty,_t_lid,nparam,mut1)
                                                                    ->
                                                                    let fv1 =
                                                                    FStar_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    (FStar_Pervasives_Native.Some
                                                                    FStar_Syntax_Syntax.Data_ctor)
                                                                     in
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_us) <>
                                                                    (FStar_List.length
                                                                    c_us))
                                                                    "t_us don't match?"
                                                                    (fun
                                                                    uu____9364
                                                                     ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us
                                                                     in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty
                                                                     in
                                                                    let uu____9369
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____9369
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____9392
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____9392
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____9411
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname
                                                                     in
                                                                    let ppname1
                                                                    =
                                                                    let uu___1299_9434
                                                                    = ppname
                                                                     in
                                                                    {
                                                                    FStar_Ident.idText
                                                                    =
                                                                    (Prims.op_Hat
                                                                    "a"
                                                                    ppname.FStar_Ident.idText);
                                                                    FStar_Ident.idRange
                                                                    =
                                                                    (uu___1299_9434.FStar_Ident.idRange)
                                                                    }  in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    (let uu___1302_9438
                                                                    = bv  in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1302_9438.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (uu___1302_9438.FStar_Syntax_Syntax.sort)
                                                                    })  in
                                                                    let bs' =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9464
                                                                     ->
                                                                    match uu____9464
                                                                    with
                                                                    | 
                                                                    (bv,aq)
                                                                    ->
                                                                    let uu____9483
                                                                    =
                                                                    rename_bv
                                                                    bv  in
                                                                    (uu____9483,
                                                                    aq)) bs
                                                                     in
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun
                                                                    uu____9508
                                                                     ->
                                                                    fun
                                                                    uu____9509
                                                                     ->
                                                                    match 
                                                                    (uu____9508,
                                                                    uu____9509)
                                                                    with
                                                                    | 
                                                                    ((bv,uu____9535),
                                                                    (bv',uu____9537))
                                                                    ->
                                                                    let uu____9558
                                                                    =
                                                                    let uu____9565
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv'  in
                                                                    (bv,
                                                                    uu____9565)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____9558)
                                                                    bs bs'
                                                                     in
                                                                    let uu____9570
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs'  in
                                                                    let uu____9579
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst1
                                                                    comp  in
                                                                    (uu____9570,
                                                                    uu____9579)
                                                                     in
                                                                    (match uu____9411
                                                                    with
                                                                    | 
                                                                    (bs1,comp1)
                                                                    ->
                                                                    let uu____9626
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    bs1  in
                                                                    (match uu____9626
                                                                    with
                                                                    | 
                                                                    (d_ps,bs2)
                                                                    ->
                                                                    let uu____9699
                                                                    =
                                                                    let uu____9701
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1  in
                                                                    Prims.op_Negation
                                                                    uu____9701
                                                                     in
                                                                    failwhen
                                                                    uu____9699
                                                                    "not total?"
                                                                    (fun
                                                                    uu____9720
                                                                     ->
                                                                    let mk_pat
                                                                    p =
                                                                    {
                                                                    FStar_Syntax_Syntax.v
                                                                    = p;
                                                                    FStar_Syntax_Syntax.p
                                                                    =
                                                                    (s_tm1.FStar_Syntax_Syntax.pos)
                                                                    }  in
                                                                    let is_imp
                                                                    uu___6_9737
                                                                    =
                                                                    match uu___6_9737
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____9741)
                                                                    -> true
                                                                    | 
                                                                    uu____9744
                                                                    -> false
                                                                     in
                                                                    let uu____9748
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____9748
                                                                    with
                                                                    | 
                                                                    (a_ps,a_is)
                                                                    ->
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_ps) <>
                                                                    (FStar_List.length
                                                                    d_ps))
                                                                    "params not match?"
                                                                    (fun
                                                                    uu____9884
                                                                     ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps
                                                                     in
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9946
                                                                     ->
                                                                    match uu____9946
                                                                    with
                                                                    | 
                                                                    ((bv,uu____9966),
                                                                    (t,uu____9968))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps
                                                                     in
                                                                    let bs3 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs2  in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____10038
                                                                     ->
                                                                    match uu____10038
                                                                    with
                                                                    | 
                                                                    ((bv,uu____10065),
                                                                    (t,uu____10067))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (bv, t))),
                                                                    true))
                                                                    d_ps_a_ps
                                                                     in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____10126
                                                                     ->
                                                                    match uu____10126
                                                                    with
                                                                    | 
                                                                    (bv,aq)
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    aq))) bs3
                                                                     in
                                                                    let subpats
                                                                    =
                                                                    FStar_List.append
                                                                    subpats_1
                                                                    subpats_2
                                                                     in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    subpats))
                                                                     in
                                                                    let env =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    let cod =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g  in
                                                                    let equ =
                                                                    env.FStar_TypeChecker_Env.universe_of
                                                                    env s_ty1
                                                                     in
                                                                    let uu____10181
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1361_10205
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1361_10205.FStar_TypeChecker_Env.erasable_types_tab)
                                                                    }) s_ty1
                                                                    pat  in
                                                                    match uu____10181
                                                                    with
                                                                    | 
                                                                    (uu____10219,uu____10220,uu____10221,uu____10222,pat_t,uu____10224,_guard_pat,_erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____10238
                                                                    =
                                                                    let uu____10239
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____10239
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____10238
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____10244
                                                                    =
                                                                    let uu____10253
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____10253]
                                                                     in
                                                                    let uu____10272
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____10244
                                                                    uu____10272
                                                                     in
                                                                    let nty =
                                                                    let uu____10278
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu____10278
                                                                     in
                                                                    let uu____10281
                                                                    =
                                                                    FStar_Tactics_Monad.new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10281
                                                                    (fun
                                                                    uu____10311
                                                                     ->
                                                                    match uu____10311
                                                                    with
                                                                    | 
                                                                    (uvt,uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false
                                                                    g.FStar_Tactics_Types.label
                                                                     in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs3
                                                                     in
                                                                    let brt1
                                                                    =
                                                                    let uu____10338
                                                                    =
                                                                    let uu____10349
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____10349]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____10338
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____10385
                                                                    =
                                                                    let uu____10396
                                                                    =
                                                                    let uu____10401
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs3)  in
                                                                    (fv1,
                                                                    uu____10401)
                                                                     in
                                                                    (g', br,
                                                                    uu____10396)
                                                                     in
                                                                    FStar_Tactics_Monad.ret
                                                                    uu____10385)))))))
                                                                    | 
                                                                    uu____10422
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids
                                                                 in
                                                              FStar_Tactics_Monad.bind
                                                                uu____9256
                                                                (fun goal_brs
                                                                    ->
                                                                   let uu____10472
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs
                                                                     in
                                                                   match uu____10472
                                                                   with
                                                                   | 
                                                                   (goals,brs,infos)
                                                                    ->
                                                                    let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    FStar_Pervasives_Native.None
                                                                    s_tm1.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let uu____10545
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10545
                                                                    (fun
                                                                    uu____10556
                                                                     ->
                                                                    let uu____10557
                                                                    =
                                                                    FStar_Tactics_Monad.add_goals
                                                                    goals  in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10557
                                                                    (fun
                                                                    uu____10567
                                                                     ->
                                                                    FStar_Tactics_Monad.ret
                                                                    infos)))))
                                            | uu____10574 ->
                                                FStar_Tactics_Monad.fail
                                                  "not an inductive type"))))))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "destruct") uu____8971
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____10623::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____10653 = init xs  in x :: uu____10653
  
let rec (inspect :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Tactics_Monad.tac)
  =
  fun t  ->
    let uu____10666 =
      let uu____10669 = top_env ()  in
      FStar_Tactics_Monad.bind uu____10669
        (fun e  ->
           let t1 = FStar_Syntax_Util.unascribe t  in
           let t2 = FStar_Syntax_Util.un_uinst t1  in
           let t3 = FStar_Syntax_Util.unlazy_emb t2  in
           match t3.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_meta (t4,uu____10685) -> inspect t4
           | FStar_Syntax_Syntax.Tm_name bv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Var bv)
           | FStar_Syntax_Syntax.Tm_bvar bv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_BVar bv)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_FVar fv)
           | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
               failwith "empty arguments on Tm_app"
           | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
               let uu____10751 = last args  in
               (match uu____10751 with
                | (a,q) ->
                    let q' = FStar_Reflection_Basic.inspect_aqual q  in
                    let uu____10781 =
                      let uu____10782 =
                        let uu____10787 =
                          let uu____10788 =
                            let uu____10793 = init args  in
                            FStar_Syntax_Syntax.mk_Tm_app hd1 uu____10793  in
                          uu____10788 FStar_Pervasives_Native.None
                            t3.FStar_Syntax_Syntax.pos
                           in
                        (uu____10787, (a, q'))  in
                      FStar_Reflection_Data.Tv_App uu____10782  in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10781)
           | FStar_Syntax_Syntax.Tm_abs ([],uu____10804,uu____10805) ->
               failwith "empty arguments on Tm_abs"
           | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
               let uu____10858 = FStar_Syntax_Subst.open_term bs t4  in
               (match uu____10858 with
                | (bs1,t5) ->
                    (match bs1 with
                     | [] -> failwith "impossible"
                     | b::bs2 ->
                         let uu____10900 =
                           let uu____10901 =
                             let uu____10906 = FStar_Syntax_Util.abs bs2 t5 k
                                in
                             (b, uu____10906)  in
                           FStar_Reflection_Data.Tv_Abs uu____10901  in
                         FStar_All.pipe_left FStar_Tactics_Monad.ret
                           uu____10900))
           | FStar_Syntax_Syntax.Tm_type uu____10909 ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Type ())
           | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
               failwith "empty binders on arrow"
           | FStar_Syntax_Syntax.Tm_arrow uu____10934 ->
               let uu____10949 = FStar_Syntax_Util.arrow_one t3  in
               (match uu____10949 with
                | FStar_Pervasives_Native.Some (b,c) ->
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Arrow (b, c))
                | FStar_Pervasives_Native.None  -> failwith "impossible")
           | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____10980 = FStar_Syntax_Subst.open_term [b] t4  in
               (match uu____10980 with
                | (b',t5) ->
                    let b1 =
                      match b' with
                      | b'1::[] -> b'1
                      | uu____11033 -> failwith "impossible"  in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Refine
                         ((FStar_Pervasives_Native.fst b1), t5)))
           | FStar_Syntax_Syntax.Tm_constant c ->
               let uu____11046 =
                 let uu____11047 = FStar_Reflection_Basic.inspect_const c  in
                 FStar_Reflection_Data.Tv_Const uu____11047  in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11046
           | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
               let uu____11068 =
                 let uu____11069 =
                   let uu____11074 =
                     let uu____11075 =
                       FStar_Syntax_Unionfind.uvar_id
                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                        in
                     FStar_BigInt.of_int_fs uu____11075  in
                   (uu____11074, (ctx_u, s))  in
                 FStar_Reflection_Data.Tv_Uvar uu____11069  in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11068
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____11115 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let b = FStar_Syntax_Syntax.mk_binder bv  in
                      let uu____11120 = FStar_Syntax_Subst.open_term [b] t21
                         in
                      (match uu____11120 with
                       | (bs,t22) ->
                           let b1 =
                             match bs with
                             | b1::[] -> b1
                             | uu____11173 ->
                                 failwith
                                   "impossible: open_term returned different amount of binders"
                              in
                           FStar_All.pipe_left FStar_Tactics_Monad.ret
                             (FStar_Reflection_Data.Tv_Let
                                (false, (lb.FStar_Syntax_Syntax.lbattrs),
                                  (FStar_Pervasives_Native.fst b1),
                                  (lb.FStar_Syntax_Syntax.lbdef), t22))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____11217 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let uu____11221 =
                        FStar_Syntax_Subst.open_let_rec [lb] t21  in
                      (match uu____11221 with
                       | (lbs,t22) ->
                           (match lbs with
                            | lb1::[] ->
                                (match lb1.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____11241 ->
                                     FStar_Tactics_Monad.ret
                                       FStar_Reflection_Data.Tv_Unknown
                                 | FStar_Util.Inl bv1 ->
                                     FStar_All.pipe_left
                                       FStar_Tactics_Monad.ret
                                       (FStar_Reflection_Data.Tv_Let
                                          (true,
                                            (lb1.FStar_Syntax_Syntax.lbattrs),
                                            bv1,
                                            (lb1.FStar_Syntax_Syntax.lbdef),
                                            t22)))
                            | uu____11249 ->
                                failwith
                                  "impossible: open_term returned different amount of binders")))
           | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
               let rec inspect_pat p =
                 match p.FStar_Syntax_Syntax.v with
                 | FStar_Syntax_Syntax.Pat_constant c ->
                     let uu____11304 = FStar_Reflection_Basic.inspect_const c
                        in
                     FStar_Reflection_Data.Pat_Constant uu____11304
                 | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                     let uu____11325 =
                       let uu____11337 =
                         FStar_List.map
                           (fun uu____11361  ->
                              match uu____11361 with
                              | (p1,b) ->
                                  let uu____11382 = inspect_pat p1  in
                                  (uu____11382, b)) ps
                          in
                       (fv, uu____11337)  in
                     FStar_Reflection_Data.Pat_Cons uu____11325
                 | FStar_Syntax_Syntax.Pat_var bv ->
                     FStar_Reflection_Data.Pat_Var bv
                 | FStar_Syntax_Syntax.Pat_wild bv ->
                     FStar_Reflection_Data.Pat_Wild bv
                 | FStar_Syntax_Syntax.Pat_dot_term (bv,t5) ->
                     FStar_Reflection_Data.Pat_Dot_Term (bv, t5)
                  in
               let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs
                  in
               let brs2 =
                 FStar_List.map
                   (fun uu___7_11478  ->
                      match uu___7_11478 with
                      | (pat,uu____11500,t5) ->
                          let uu____11518 = inspect_pat pat  in
                          (uu____11518, t5)) brs1
                  in
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Match (t4, brs2))
           | FStar_Syntax_Syntax.Tm_unknown  ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 FStar_Reflection_Data.Tv_Unknown
           | uu____11527 ->
               ((let uu____11529 =
                   let uu____11535 =
                     let uu____11537 = FStar_Syntax_Print.tag_of_term t3  in
                     let uu____11539 = term_to_string e t3  in
                     FStar_Util.format2
                       "inspect: outside of expected syntax (%s, %s)\n"
                       uu____11537 uu____11539
                      in
                   (FStar_Errors.Warning_CantInspect, uu____11535)  in
                 FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos
                   uu____11529);
                FStar_All.pipe_left FStar_Tactics_Monad.ret
                  FStar_Reflection_Data.Tv_Unknown))
       in
    FStar_Tactics_Monad.wrap_err "inspect" uu____10666
  
let (pack :
  FStar_Reflection_Data.term_view ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____11557 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11557
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____11561 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11561
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____11565 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11565
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____11572 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11572
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____11597 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11597
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____11614 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11614
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left FStar_Tactics_Monad.ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____11633 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11633
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____11637 =
          let uu____11638 =
            let uu____11645 =
              let uu____11646 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____11646  in
            FStar_Syntax_Syntax.mk uu____11645  in
          uu____11638 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11637
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____11651 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11651
    | FStar_Reflection_Data.Tv_Let (false ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____11665 =
          let uu____11666 =
            let uu____11673 =
              let uu____11674 =
                let uu____11688 =
                  let uu____11691 =
                    let uu____11692 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____11692]  in
                  FStar_Syntax_Subst.close uu____11691 t2  in
                ((false, [lb]), uu____11688)  in
              FStar_Syntax_Syntax.Tm_let uu____11674  in
            FStar_Syntax_Syntax.mk uu____11673  in
          uu____11666 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11665
    | FStar_Reflection_Data.Tv_Let (true ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____11737 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____11737 with
         | (lbs,body) ->
             let uu____11752 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11752)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____11789 =
                let uu____11790 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____11790  in
              FStar_All.pipe_left wrap uu____11789
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____11807 =
                let uu____11808 =
                  let uu____11822 =
                    FStar_List.map
                      (fun uu____11846  ->
                         match uu____11846 with
                         | (p1,b) ->
                             let uu____11861 = pack_pat p1  in
                             (uu____11861, b)) ps
                     in
                  (fv, uu____11822)  in
                FStar_Syntax_Syntax.Pat_cons uu____11808  in
              FStar_All.pipe_left wrap uu____11807
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv,t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1))
           in
        let brs1 =
          FStar_List.map
            (fun uu___8_11909  ->
               match uu___8_11909 with
               | (pat,t1) ->
                   let uu____11926 = pack_pat pat  in
                   (uu____11926, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____11974 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11974
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____12002 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____12002
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____12048 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____12048
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____12087 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____12087
  
let (lget :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty  ->
    fun k  ->
      let uu____12107 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps  ->
             let uu____12113 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____12113 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Tactics_Monad.fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lget") uu____12107
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____12147 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps  ->
               let ps1 =
                 let uu___1666_12154 = ps  in
                 let uu____12155 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___1666_12154.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___1666_12154.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___1666_12154.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___1666_12154.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___1666_12154.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___1666_12154.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___1666_12154.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___1666_12154.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___1666_12154.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___1666_12154.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___1666_12154.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____12155
                 }  in
               FStar_Tactics_Monad.set ps1)
           in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lset") uu____12147
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____12182 =
        FStar_TypeChecker_Env.new_implicit_var_aux "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
          FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
         in
      match uu____12182 with
      | (u,ctx_uvars,g_u) ->
          let uu____12219 = FStar_List.hd ctx_uvars  in
          (match uu____12219 with
           | (ctx_uvar,uu____12233) ->
               let g =
                 let uu____12235 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____12235 false
                   ""
                  in
               (g, g_u))
  
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu____12244 = FStar_TypeChecker_Env.clear_expected_typ env  in
    match uu____12244 with
    | (env1,uu____12252) ->
        let env2 =
          let uu___1683_12258 = env1  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1683_12258.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1683_12258.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1683_12258.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1683_12258.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1683_12258.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1683_12258.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1683_12258.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1683_12258.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1683_12258.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1683_12258.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___1683_12258.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1683_12258.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1683_12258.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1683_12258.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1683_12258.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1683_12258.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1683_12258.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1683_12258.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1683_12258.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1683_12258.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1683_12258.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1683_12258.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1683_12258.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1683_12258.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1683_12258.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1683_12258.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1683_12258.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1683_12258.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1683_12258.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1683_12258.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1683_12258.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1683_12258.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1683_12258.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1683_12258.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1683_12258.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1683_12258.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1683_12258.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1683_12258.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1683_12258.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1683_12258.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1683_12258.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1683_12258.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1683_12258.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1683_12258.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1683_12258.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1683_12258.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let env3 =
          let uu___1686_12261 = env2  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1686_12261.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1686_12261.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1686_12261.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1686_12261.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1686_12261.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1686_12261.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1686_12261.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1686_12261.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1686_12261.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1686_12261.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1686_12261.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1686_12261.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1686_12261.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1686_12261.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1686_12261.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1686_12261.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1686_12261.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1686_12261.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1686_12261.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1686_12261.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1686_12261.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1686_12261.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1686_12261.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___1686_12261.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1686_12261.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1686_12261.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1686_12261.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1686_12261.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1686_12261.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1686_12261.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1686_12261.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1686_12261.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1686_12261.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1686_12261.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1686_12261.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1686_12261.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1686_12261.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1686_12261.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1686_12261.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1686_12261.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1686_12261.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1686_12261.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1686_12261.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1686_12261.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1686_12261.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1686_12261.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        env3
  
let (proofstate_of_goals :
  FStar_Range.range ->
    env ->
      FStar_Tactics_Types.goal Prims.list ->
        FStar_TypeChecker_Common.implicit Prims.list ->
          FStar_Tactics_Types.proofstate)
  =
  fun rng  ->
    fun env  ->
      fun goals  ->
        fun imps  ->
          let env1 = tac_env env  in
          let ps =
            let uu____12294 =
              FStar_TypeChecker_Env.debug env1
                (FStar_Options.Other "TacVerbose")
               in
            let uu____12297 = FStar_Util.psmap_empty ()  in
            {
              FStar_Tactics_Types.main_context = env1;
              FStar_Tactics_Types.all_implicits = imps;
              FStar_Tactics_Types.goals = goals;
              FStar_Tactics_Types.smt_goals = [];
              FStar_Tactics_Types.depth = Prims.int_zero;
              FStar_Tactics_Types.__dump =
                FStar_Tactics_Printing.do_dump_proofstate;
              FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
              FStar_Tactics_Types.entry_range = rng;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
              FStar_Tactics_Types.freshness = Prims.int_zero;
              FStar_Tactics_Types.tac_verb_dbg = uu____12294;
              FStar_Tactics_Types.local_state = uu____12297
            }  in
          ps
  
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng  ->
    fun env  ->
      fun typ  ->
        let env1 = tac_env env  in
        let uu____12323 = goal_of_goal_ty env1 typ  in
        match uu____12323 with
        | (g,g_u) ->
            let ps =
              proofstate_of_goals rng env1 [g]
                g_u.FStar_TypeChecker_Common.implicits
               in
            let uu____12335 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____12335)
  
let (goal_of_implicit :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicit -> FStar_Tactics_Types.goal)
  =
  fun env  ->
    fun i  ->
      let uu____12347 = FStar_Options.peek ()  in
      FStar_Tactics_Types.mk_goal env i.FStar_TypeChecker_Common.imp_uvar
        uu____12347 false ""
  
let (proofstate_of_all_implicits :
  FStar_Range.range ->
    env ->
      implicits ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng  ->
    fun env  ->
      fun imps  ->
        let goals = FStar_List.map (goal_of_implicit env) imps  in
        let w =
          let uu____12374 = FStar_List.hd goals  in
          FStar_Tactics_Types.goal_witness uu____12374  in
        let ps =
          let uu____12376 =
            FStar_TypeChecker_Env.debug env
              (FStar_Options.Other "TacVerbose")
             in
          let uu____12379 = FStar_Util.psmap_empty ()  in
          {
            FStar_Tactics_Types.main_context = env;
            FStar_Tactics_Types.all_implicits = imps;
            FStar_Tactics_Types.goals = goals;
            FStar_Tactics_Types.smt_goals = [];
            FStar_Tactics_Types.depth = Prims.int_zero;
            FStar_Tactics_Types.__dump =
              (fun ps  ->
                 fun msg  -> FStar_Tactics_Printing.do_dump_proofstate ps msg);
            FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
            FStar_Tactics_Types.entry_range = rng;
            FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
            FStar_Tactics_Types.freshness = Prims.int_zero;
            FStar_Tactics_Types.tac_verb_dbg = uu____12376;
            FStar_Tactics_Types.local_state = uu____12379
          }  in
        (ps, w)
  