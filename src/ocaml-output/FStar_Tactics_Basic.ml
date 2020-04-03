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
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g  ->
    let uu____53 =
      let uu____54 = FStar_Tactics_Types.goal_env g  in
      let uu____55 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____54 uu____55  in
    FStar_Tactics_Types.goal_with_type g uu____53
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____80 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____80
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____105 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____105
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____137 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____137
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____150 =
      let uu____151 = FStar_Tactics_Types.goal_env g  in
      let uu____152 = FStar_Tactics_Types.goal_type g  in
      whnf uu____151 uu____152  in
    FStar_Syntax_Util.un_squash uu____150
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____161 = get_phi g  in FStar_Option.isSome uu____161 
let (print : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg  ->
    (let uu____177 =
       let uu____179 = FStar_Options.silent ()  in
       Prims.op_Negation uu____179  in
     if uu____177 then tacprint msg else ());
    FStar_Tactics_Monad.ret ()
  
let (debugging : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____192  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps  ->
         let uu____200 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         FStar_Tactics_Monad.ret uu____200)
  
let (dump : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg  ->
    FStar_Tactics_Monad.mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____224 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          FStar_Tactics_Printing.do_dump_proofstate uu____224 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let fail1 :
  'Auu____232 .
    Prims.string -> Prims.string -> 'Auu____232 FStar_Tactics_Monad.tac
  =
  fun msg  ->
    fun x  ->
      let uu____249 = FStar_Util.format1 msg x  in
      FStar_Tactics_Monad.fail uu____249
  
let fail2 :
  'Auu____260 .
    Prims.string ->
      Prims.string -> Prims.string -> 'Auu____260 FStar_Tactics_Monad.tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____284 = FStar_Util.format2 msg x y  in
        FStar_Tactics_Monad.fail uu____284
  
let fail3 :
  'Auu____297 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> 'Auu____297 FStar_Tactics_Monad.tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____328 = FStar_Util.format3 msg x y z  in
          FStar_Tactics_Monad.fail uu____328
  
let fail4 :
  'Auu____343 .
    Prims.string ->
      Prims.string ->
        Prims.string ->
          Prims.string -> Prims.string -> 'Auu____343 FStar_Tactics_Monad.tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____381 = FStar_Util.format4 msg x y z w  in
            FStar_Tactics_Monad.fail uu____381
  
let catch :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (Prims.exn,'a) FStar_Util.either FStar_Tactics_Monad.tac
  =
  fun t  ->
    FStar_Tactics_Monad.mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____416 = FStar_Tactics_Monad.run t ps  in
         match uu____416 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___68_440 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___68_440.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___68_440.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___68_440.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___68_440.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___68_440.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___68_440.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___68_440.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___68_440.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___68_440.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___68_440.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___68_440.FStar_Tactics_Types.local_state)
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
         let uu____479 = FStar_Tactics_Monad.run t ps  in
         match uu____479 with
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
    let uu____527 = catch t  in
    FStar_Tactics_Monad.bind uu____527
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 ->
             FStar_Tactics_Monad.ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____554 ->
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
           (fun uu___94_586  ->
              match () with
              | () ->
                  let uu____591 = trytac t  in
                  FStar_Tactics_Monad.run uu____591 ps) ()
         with
         | FStar_Errors.Err (uu____607,msg) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____613  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____619,msg,uu____621) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____626  ->
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
        (let uu____655 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____655
         then
           let uu____659 = FStar_Syntax_Print.term_to_string t1  in
           let uu____661 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____659
             uu____661
         else ());
        (try
           (fun uu___114_672  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____680 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____680
                    then
                      let uu____684 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____686 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____688 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____684
                        uu____686 uu____688
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Tactics_Monad.ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____699 =
                          FStar_Tactics_Monad.add_implicits
                            g.FStar_TypeChecker_Common.implicits
                           in
                        FStar_Tactics_Monad.bind uu____699
                          (fun uu____704  -> FStar_Tactics_Monad.ret true))))
             ()
         with
         | FStar_Errors.Err (uu____714,msg) ->
             FStar_Tactics_Monad.mlog
               (fun uu____720  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____723  -> FStar_Tactics_Monad.ret false)
         | FStar_Errors.Error (uu____726,msg,r) ->
             FStar_Tactics_Monad.mlog
               (fun uu____734  ->
                  let uu____735 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____735)
               (fun uu____739  -> FStar_Tactics_Monad.ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____768  ->
             (let uu____770 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____770
              then
                (FStar_Options.push ();
                 (let uu____775 =
                    FStar_Options.set_options
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____779 = __do_unify env t1 t2  in
              FStar_Tactics_Monad.bind uu____779
                (fun r  ->
                   (let uu____790 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____790 then FStar_Options.pop () else ());
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
        let uu____822 = do_unify env t1 t2  in
        FStar_Tactics_Monad.bind uu____822
          (fun r  ->
             if r
             then
               let uvs2 = FStar_Syntax_Free.uvars_uncached t1  in
               let uu____840 =
                 let uu____842 = FStar_Util.set_eq uvs1 uvs2  in
                 Prims.op_Negation uu____842  in
               (if uu____840
                then FStar_Tactics_Monad.ret false
                else FStar_Tactics_Monad.ret true)
             else FStar_Tactics_Monad.ret false)
  
let (set_solution :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal  ->
    fun solution  ->
      let uu____873 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____873 with
      | FStar_Pervasives_Native.Some uu____878 ->
          let uu____879 =
            let uu____881 =
              FStar_Tactics_Printing.goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____881  in
          FStar_Tactics_Monad.fail uu____879
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
      let uu____902 = FStar_Tactics_Types.goal_env goal  in
      let uu____903 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____902 solution uu____903
  
let (solve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      FStar_Tactics_Monad.mlog
        (fun uu____923  ->
           let uu____924 =
             let uu____926 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____926  in
           let uu____927 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____924 uu____927)
        (fun uu____932  ->
           let uu____933 = trysolve goal solution  in
           FStar_Tactics_Monad.bind uu____933
             (fun b  ->
                if b
                then
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____945  ->
                       FStar_Tactics_Monad.remove_solved_goals)
                else
                  (let uu____948 =
                     let uu____950 =
                       let uu____952 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____952 solution  in
                     let uu____953 =
                       let uu____955 = FStar_Tactics_Types.goal_env goal  in
                       let uu____956 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____955 uu____956  in
                     let uu____957 =
                       let uu____959 = FStar_Tactics_Types.goal_env goal  in
                       let uu____960 = FStar_Tactics_Types.goal_type goal  in
                       tts uu____959 uu____960  in
                     FStar_Util.format3 "%s does not solve %s : %s" uu____950
                       uu____953 uu____957
                      in
                   FStar_Tactics_Monad.fail uu____948)))
  
let (solve' :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal  ->
    fun solution  ->
      let uu____977 = set_solution goal solution  in
      FStar_Tactics_Monad.bind uu____977
        (fun uu____981  ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
             (fun uu____983  -> FStar_Tactics_Monad.remove_solved_goals))
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____992 = FStar_Syntax_Util.un_squash t1  in
    match uu____992 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____1004 =
          let uu____1005 = FStar_Syntax_Subst.compress t'1  in
          uu____1005.FStar_Syntax_Syntax.n  in
        (match uu____1004 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1010 -> false)
    | uu____1012 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1025 = FStar_Syntax_Util.un_squash t  in
    match uu____1025 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1036 =
          let uu____1037 = FStar_Syntax_Subst.compress t'  in
          uu____1037.FStar_Syntax_Syntax.n  in
        (match uu____1036 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1042 -> false)
    | uu____1044 -> false
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t  ->
    let uu____1060 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps  ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g  ->
                (let uu____1069 =
                   let uu____1070 = FStar_Tactics_Types.goal_type g  in
                   uu____1070.FStar_Syntax_Syntax.pos  in
                 let uu____1073 =
                   let uu____1079 =
                     let uu____1081 =
                       FStar_Tactics_Printing.goal_to_string ""
                         FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1081
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1079)  in
                 FStar_Errors.log_issue uu____1069 uu____1073);
                solve' g t))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tadmit_t") uu____1060
  
let (fresh : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1104  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___200_1115 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___200_1115.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (uu___200_1115.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___200_1115.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___200_1115.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___200_1115.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___200_1115.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___200_1115.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___200_1115.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___200_1115.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___200_1115.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___200_1115.FStar_Tactics_Types.local_state)
           }  in
         let uu____1117 = FStar_Tactics_Monad.set ps1  in
         FStar_Tactics_Monad.bind uu____1117
           (fun uu____1122  ->
              let uu____1123 = FStar_BigInt.of_int_fs n1  in
              FStar_Tactics_Monad.ret uu____1123))
  
let (curms : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1131  ->
    let uu____1134 =
      let uu____1135 = FStar_Util.now_ms ()  in
      FStar_All.pipe_right uu____1135 FStar_BigInt.of_int_fs  in
    FStar_Tactics_Monad.ret uu____1134
  
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
             (fun uu____1181  ->
                let uu____1182 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1182)
             (fun uu____1187  ->
                let e1 =
                  let uu___209_1189 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___209_1189.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___209_1189.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___209_1189.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___209_1189.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___209_1189.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___209_1189.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___209_1189.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___209_1189.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___209_1189.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___209_1189.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___209_1189.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___209_1189.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___209_1189.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___209_1189.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___209_1189.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___209_1189.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___209_1189.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___209_1189.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___209_1189.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___209_1189.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___209_1189.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___209_1189.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___209_1189.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___209_1189.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___209_1189.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___209_1189.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___209_1189.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___209_1189.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___209_1189.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___209_1189.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___209_1189.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___209_1189.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___209_1189.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___209_1189.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___209_1189.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___209_1189.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___209_1189.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___209_1189.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___209_1189.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___209_1189.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___209_1189.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___209_1189.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___209_1189.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___209_1189.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___209_1189.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___209_1189.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___213_1201  ->
                     match () with
                     | () ->
                         let uu____1210 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         FStar_Tactics_Monad.ret uu____1210) ()
                with
                | FStar_Errors.Err (uu____1237,msg) ->
                    let uu____1241 = tts e1 t  in
                    let uu____1243 =
                      let uu____1245 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____1245
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1241 uu____1243 msg
                | FStar_Errors.Error (uu____1255,msg,uu____1257) ->
                    let uu____1260 = tts e1 t  in
                    let uu____1262 =
                      let uu____1264 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____1264
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1260 uu____1262 msg))
  
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
             (fun uu____1317  ->
                let uu____1318 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____1318)
             (fun uu____1323  ->
                let e1 =
                  let uu___230_1325 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___230_1325.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___230_1325.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___230_1325.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___230_1325.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___230_1325.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___230_1325.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___230_1325.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___230_1325.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___230_1325.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___230_1325.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___230_1325.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___230_1325.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___230_1325.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___230_1325.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___230_1325.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___230_1325.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___230_1325.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___230_1325.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___230_1325.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___230_1325.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___230_1325.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___230_1325.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___230_1325.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___230_1325.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___230_1325.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___230_1325.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___230_1325.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___230_1325.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___230_1325.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___230_1325.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___230_1325.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___230_1325.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___230_1325.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___230_1325.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___230_1325.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___230_1325.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___230_1325.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___230_1325.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___230_1325.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___230_1325.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___230_1325.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___230_1325.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___230_1325.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___230_1325.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___230_1325.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___230_1325.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___234_1340  ->
                     match () with
                     | () ->
                         let uu____1349 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____1349 with
                          | (t1,lc,g) ->
                              FStar_Tactics_Monad.ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu____1387,msg) ->
                    let uu____1391 = tts e1 t  in
                    let uu____1393 =
                      let uu____1395 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____1395
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1391 uu____1393 msg
                | FStar_Errors.Error (uu____1405,msg,uu____1407) ->
                    let uu____1410 = tts e1 t  in
                    let uu____1412 =
                      let uu____1414 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____1414
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1410 uu____1412 msg))
  
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
             (fun uu____1467  ->
                let uu____1468 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_lax(%s)\n" uu____1468)
             (fun uu____1474  ->
                let e1 =
                  let uu___255_1476 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___255_1476.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___255_1476.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___255_1476.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___255_1476.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___255_1476.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___255_1476.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___255_1476.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___255_1476.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___255_1476.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___255_1476.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___255_1476.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___255_1476.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___255_1476.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___255_1476.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___255_1476.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___255_1476.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___255_1476.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___255_1476.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___255_1476.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___255_1476.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___255_1476.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___255_1476.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___255_1476.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___255_1476.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___255_1476.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___255_1476.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___255_1476.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___255_1476.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___255_1476.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___255_1476.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___255_1476.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___255_1476.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___255_1476.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___255_1476.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___255_1476.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___255_1476.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___255_1476.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___255_1476.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___255_1476.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___255_1476.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___255_1476.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___255_1476.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___255_1476.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___255_1476.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___255_1476.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___255_1476.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                let e2 =
                  let uu___258_1479 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___258_1479.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___258_1479.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___258_1479.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___258_1479.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___258_1479.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___258_1479.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___258_1479.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___258_1479.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___258_1479.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___258_1479.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___258_1479.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___258_1479.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___258_1479.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___258_1479.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___258_1479.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___258_1479.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___258_1479.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___258_1479.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___258_1479.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___258_1479.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___258_1479.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___258_1479.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___258_1479.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___258_1479.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___258_1479.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___258_1479.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___258_1479.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___258_1479.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___258_1479.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___258_1479.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___258_1479.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___258_1479.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___258_1479.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___258_1479.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___258_1479.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___258_1479.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___258_1479.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___258_1479.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___258_1479.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___258_1479.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___258_1479.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___258_1479.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___258_1479.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___258_1479.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___258_1479.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___258_1479.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___262_1491  ->
                     match () with
                     | () ->
                         let uu____1500 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         FStar_Tactics_Monad.ret uu____1500) ()
                with
                | FStar_Errors.Err (uu____1527,msg) ->
                    let uu____1531 = tts e2 t  in
                    let uu____1533 =
                      let uu____1535 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____1535
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1531 uu____1533 msg
                | FStar_Errors.Error (uu____1545,msg,uu____1547) ->
                    let uu____1550 = tts e2 t  in
                    let uu____1552 =
                      let uu____1554 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____1554
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1550 uu____1552 msg))
  
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
  fun uu____1588  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps  -> FStar_Tactics_Monad.ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy :
  FStar_Tactics_Types.guard_policy -> unit FStar_Tactics_Monad.tac) =
  fun pol  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps  ->
         FStar_Tactics_Monad.set
           (let uu___283_1607 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___283_1607.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___283_1607.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___283_1607.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___283_1607.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___283_1607.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___283_1607.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___283_1607.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___283_1607.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___283_1607.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___283_1607.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___283_1607.FStar_Tactics_Types.local_state)
            }))
  
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun pol  ->
    fun t  ->
      let uu____1632 = get_guard_policy ()  in
      FStar_Tactics_Monad.bind uu____1632
        (fun old_pol  ->
           let uu____1638 = set_guard_policy pol  in
           FStar_Tactics_Monad.bind uu____1638
             (fun uu____1642  ->
                FStar_Tactics_Monad.bind t
                  (fun r  ->
                     let uu____1646 = set_guard_policy old_pol  in
                     FStar_Tactics_Monad.bind uu____1646
                       (fun uu____1650  -> FStar_Tactics_Monad.ret r))))
  
let (getopts : FStar_Options.optionstate FStar_Tactics_Monad.tac) =
  let uu____1654 = trytac FStar_Tactics_Monad.cur_goal  in
  FStar_Tactics_Monad.bind uu____1654
    (fun uu___0_1663  ->
       match uu___0_1663 with
       | FStar_Pervasives_Native.Some g ->
           FStar_Tactics_Monad.ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____1669 = FStar_Options.peek ()  in
           FStar_Tactics_Monad.ret uu____1669)
  
let (proc_guard :
  Prims.string ->
    env -> FStar_TypeChecker_Common.guard_t -> unit FStar_Tactics_Monad.tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        FStar_Tactics_Monad.mlog
          (fun uu____1694  ->
             let uu____1695 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____1695)
          (fun uu____1700  ->
             let uu____1701 =
               FStar_Tactics_Monad.add_implicits
                 g.FStar_TypeChecker_Common.implicits
                in
             FStar_Tactics_Monad.bind uu____1701
               (fun uu____1705  ->
                  FStar_Tactics_Monad.bind getopts
                    (fun opts  ->
                       let uu____1709 =
                         let uu____1710 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____1710.FStar_TypeChecker_Common.guard_f  in
                       match uu____1709 with
                       | FStar_TypeChecker_Common.Trivial  ->
                           FStar_Tactics_Monad.ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____1714 = istrivial e f  in
                           if uu____1714
                           then FStar_Tactics_Monad.ret ()
                           else
                             FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____1727 =
                                          let uu____1733 =
                                            let uu____1735 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____1735
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____1733)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____1727);
                                       FStar_Tactics_Monad.ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1741  ->
                                           let uu____1742 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____1742)
                                        (fun uu____1747  ->
                                           let uu____1748 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts ""
                                              in
                                           FStar_Tactics_Monad.bind
                                             uu____1748
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___312_1756 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___312_1756.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___312_1756.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___312_1756.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___312_1756.FStar_Tactics_Types.label)
                                                  }  in
                                                FStar_Tactics_Monad.push_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1760  ->
                                           let uu____1761 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____1761)
                                        (fun uu____1766  ->
                                           let uu____1767 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts ""
                                              in
                                           FStar_Tactics_Monad.bind
                                             uu____1767
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___319_1775 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___319_1775.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___319_1775.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___319_1775.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___319_1775.FStar_Tactics_Types.label)
                                                  }  in
                                                FStar_Tactics_Monad.push_smt_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1779  ->
                                           let uu____1780 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____1780)
                                        (fun uu____1784  ->
                                           try
                                             (fun uu___326_1789  ->
                                                match () with
                                                | () ->
                                                    let uu____1792 =
                                                      let uu____1794 =
                                                        let uu____1796 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____1796
                                                         in
                                                      Prims.op_Negation
                                                        uu____1794
                                                       in
                                                    if uu____1792
                                                    then
                                                      FStar_Tactics_Monad.mlog
                                                        (fun uu____1803  ->
                                                           let uu____1804 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____1804)
                                                        (fun uu____1808  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else
                                                      FStar_Tactics_Monad.ret
                                                        ()) ()
                                           with
                                           | uu___325_1813 ->
                                               FStar_Tactics_Monad.mlog
                                                 (fun uu____1818  ->
                                                    let uu____1819 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____1819)
                                                 (fun uu____1823  ->
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
      let uu____1840 =
        let uu____1843 = __tc_lax e t  in
        FStar_Tactics_Monad.bind uu____1843
          (fun uu____1863  ->
             match uu____1863 with
             | (uu____1872,lc,uu____1874) ->
                 let uu____1875 =
                   let uu____1876 = FStar_TypeChecker_Common.lcomp_comp lc
                      in
                   FStar_All.pipe_right uu____1876
                     FStar_Pervasives_Native.fst
                    in
                 FStar_Tactics_Monad.ret uu____1875)
         in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tcc") uu____1840
  
let (tc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Reflection_Data.typ FStar_Tactics_Monad.tac)
  =
  fun e  ->
    fun t  ->
      let uu____1905 =
        let uu____1910 = tcc e t  in
        FStar_Tactics_Monad.bind uu____1910
          (fun c  ->
             FStar_Tactics_Monad.ret (FStar_Syntax_Util.comp_result c))
         in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tc") uu____1905
  
let (trivial : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____1935  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal  ->
         let uu____1941 =
           let uu____1943 = FStar_Tactics_Types.goal_env goal  in
           let uu____1944 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____1943 uu____1944  in
         if uu____1941
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____1950 =
              let uu____1952 = FStar_Tactics_Types.goal_env goal  in
              let uu____1953 = FStar_Tactics_Types.goal_type goal  in
              tts uu____1952 uu____1953  in
            fail1 "Not a trivial goal: %s" uu____1950))
  
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
             let uu____2004 =
               try
                 (fun uu___379_2027  ->
                    match () with
                    | () ->
                        let uu____2038 =
                          let uu____2047 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2047
                            p.FStar_Tactics_Types.goals
                           in
                        FStar_Tactics_Monad.ret uu____2038) ()
               with
               | uu___378_2058 ->
                   FStar_Tactics_Monad.fail "divide: not enough goals"
                in
             FStar_Tactics_Monad.bind uu____2004
               (fun uu____2095  ->
                  match uu____2095 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___361_2121 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___361_2121.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___361_2121.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___361_2121.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___361_2121.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___361_2121.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___361_2121.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___361_2121.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___361_2121.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___361_2121.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___361_2121.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2122 = FStar_Tactics_Monad.set lp  in
                      FStar_Tactics_Monad.bind uu____2122
                        (fun uu____2130  ->
                           FStar_Tactics_Monad.bind l
                             (fun a  ->
                                FStar_Tactics_Monad.bind
                                  FStar_Tactics_Monad.get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___367_2146 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___367_2146.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___367_2146.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___367_2146.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___367_2146.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___367_2146.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___367_2146.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___367_2146.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___367_2146.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___367_2146.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___367_2146.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____2147 =
                                       FStar_Tactics_Monad.set rp  in
                                     FStar_Tactics_Monad.bind uu____2147
                                       (fun uu____2155  ->
                                          FStar_Tactics_Monad.bind r
                                            (fun b  ->
                                               FStar_Tactics_Monad.bind
                                                 FStar_Tactics_Monad.get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___373_2171 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___373_2171.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___373_2171.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___373_2171.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___373_2171.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___373_2171.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___373_2171.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___373_2171.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___373_2171.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___373_2171.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___373_2171.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____2172 =
                                                      FStar_Tactics_Monad.set
                                                        p'
                                                       in
                                                    FStar_Tactics_Monad.bind
                                                      uu____2172
                                                      (fun uu____2180  ->
                                                         FStar_Tactics_Monad.bind
                                                           FStar_Tactics_Monad.remove_solved_goals
                                                           (fun uu____2186 
                                                              ->
                                                              FStar_Tactics_Monad.ret
                                                                (a, b)))))))))))
  
let focus : 'a . 'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac =
  fun f  ->
    let uu____2208 = divide FStar_BigInt.one f FStar_Tactics_Monad.idtac  in
    FStar_Tactics_Monad.bind uu____2208
      (fun uu____2221  ->
         match uu____2221 with | (a,()) -> FStar_Tactics_Monad.ret a)
  
let rec map :
  'a . 'a FStar_Tactics_Monad.tac -> 'a Prims.list FStar_Tactics_Monad.tac =
  fun tau  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> FStar_Tactics_Monad.ret []
         | uu____2259::uu____2260 ->
             let uu____2263 =
               let uu____2272 = map tau  in
               divide FStar_BigInt.one tau uu____2272  in
             FStar_Tactics_Monad.bind uu____2263
               (fun uu____2290  ->
                  match uu____2290 with
                  | (h,t) -> FStar_Tactics_Monad.ret (h :: t)))
  
let (seq :
  unit FStar_Tactics_Monad.tac ->
    unit FStar_Tactics_Monad.tac -> unit FStar_Tactics_Monad.tac)
  =
  fun t1  ->
    fun t2  ->
      let uu____2332 =
        FStar_Tactics_Monad.bind t1
          (fun uu____2337  ->
             let uu____2338 = map t2  in
             FStar_Tactics_Monad.bind uu____2338
               (fun uu____2346  -> FStar_Tactics_Monad.ret ()))
         in
      focus uu____2332
  
let (intro : unit -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac) =
  fun uu____2356  ->
    let uu____2359 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal  ->
           let uu____2368 =
             let uu____2375 =
               let uu____2376 = FStar_Tactics_Types.goal_env goal  in
               let uu____2377 = FStar_Tactics_Types.goal_type goal  in
               whnf uu____2376 uu____2377  in
             FStar_Syntax_Util.arrow_one uu____2375  in
           match uu____2368 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2386 =
                 let uu____2388 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2388  in
               if uu____2386
               then FStar_Tactics_Monad.fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2397 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2397 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____2413 =
                    FStar_Tactics_Monad.new_uvar "intro" env' typ'  in
                  FStar_Tactics_Monad.bind uu____2413
                    (fun uu____2430  ->
                       match uu____2430 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____2454 = set_solution goal sol  in
                           FStar_Tactics_Monad.bind uu____2454
                             (fun uu____2460  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____2462 =
                                  let uu____2465 = bnorm_goal g  in
                                  FStar_Tactics_Monad.replace_cur uu____2465
                                   in
                                FStar_Tactics_Monad.bind uu____2462
                                  (fun uu____2467  ->
                                     FStar_Tactics_Monad.ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____2472 =
                 let uu____2474 = FStar_Tactics_Types.goal_env goal  in
                 let uu____2475 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____2474 uu____2475  in
               fail1 "goal is not an arrow (%s)" uu____2472)
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "intro") uu____2359
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder)
      FStar_Tactics_Monad.tac)
  =
  fun uu____2493  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2516 =
            let uu____2523 =
              let uu____2524 = FStar_Tactics_Types.goal_env goal  in
              let uu____2525 = FStar_Tactics_Types.goal_type goal  in
              whnf uu____2524 uu____2525  in
            FStar_Syntax_Util.arrow_one uu____2523  in
          match uu____2516 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____2538 =
                let uu____2540 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____2540  in
              if uu____2538
              then FStar_Tactics_Monad.fail "Codomain is effectful"
              else
                (let bv =
                   let uu____2557 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____2557
                    in
                 let bs =
                   let uu____2568 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2568; b]  in
                 let env' =
                   let uu____2594 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____2594 bs  in
                 let uu____2595 =
                   FStar_Tactics_Monad.new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 FStar_Tactics_Monad.bind uu____2595
                   (fun uu____2621  ->
                      match uu____2621 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____2635 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____2638 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____2635
                              FStar_Parser_Const.effect_Tot_lid uu____2638 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____2656 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____2656 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____2678 =
                                   let uu____2679 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____2679.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____2678
                                  in
                               let uu____2695 = set_solution goal tm  in
                               FStar_Tactics_Monad.bind uu____2695
                                 (fun uu____2704  ->
                                    let uu____2705 =
                                      let uu____2708 =
                                        bnorm_goal
                                          (let uu___444_2711 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___444_2711.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___444_2711.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___444_2711.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___444_2711.FStar_Tactics_Types.label)
                                           })
                                         in
                                      FStar_Tactics_Monad.replace_cur
                                        uu____2708
                                       in
                                    FStar_Tactics_Monad.bind uu____2705
                                      (fun uu____2718  ->
                                         let uu____2719 =
                                           let uu____2724 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____2724, b)  in
                                         FStar_Tactics_Monad.ret uu____2719)))))
          | FStar_Pervasives_Native.None  ->
              let uu____2733 =
                let uu____2735 = FStar_Tactics_Types.goal_env goal  in
                let uu____2736 = FStar_Tactics_Types.goal_type goal  in
                tts uu____2735 uu____2736  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2733))
  
let (norm :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    unit FStar_Tactics_Monad.tac)
  =
  fun s  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal  ->
         FStar_Tactics_Monad.mlog
           (fun uu____2760  ->
              let uu____2761 =
                let uu____2763 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____2763  in
              FStar_Util.print1 "norm: witness = %s\n" uu____2761)
           (fun uu____2769  ->
              let steps =
                let uu____2773 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____2773
                 in
              let t =
                let uu____2777 = FStar_Tactics_Types.goal_env goal  in
                let uu____2778 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____2777 uu____2778  in
              let uu____2779 = FStar_Tactics_Types.goal_with_type goal t  in
              FStar_Tactics_Monad.replace_cur uu____2779))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2804 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____2812 -> g.FStar_Tactics_Types.opts
                 | uu____2815 -> FStar_Options.peek ()  in
               FStar_Tactics_Monad.mlog
                 (fun uu____2820  ->
                    let uu____2821 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____2821)
                 (fun uu____2826  ->
                    let uu____2827 = __tc_lax e t  in
                    FStar_Tactics_Monad.bind uu____2827
                      (fun uu____2848  ->
                         match uu____2848 with
                         | (t1,uu____2858,uu____2859) ->
                             let steps =
                               let uu____2863 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____2863
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             FStar_Tactics_Monad.mlog
                               (fun uu____2869  ->
                                  let uu____2870 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____2870)
                               (fun uu____2874  -> FStar_Tactics_Monad.ret t2))))
           in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_term")
          uu____2804
  
let (refine_intro : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____2887  ->
    let uu____2890 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g  ->
           let uu____2897 =
             let uu____2908 = FStar_Tactics_Types.goal_env g  in
             let uu____2909 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____2908 uu____2909
              in
           match uu____2897 with
           | (uu____2912,FStar_Pervasives_Native.None ) ->
               FStar_Tactics_Monad.fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____2938 =
                 let uu____2943 =
                   let uu____2948 =
                     let uu____2949 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____2949]  in
                   FStar_Syntax_Subst.open_term uu____2948 phi  in
                 match uu____2943 with
                 | (bvs,phi1) ->
                     let uu____2974 =
                       let uu____2975 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____2975  in
                     (uu____2974, phi1)
                  in
               (match uu____2938 with
                | (bv1,phi1) ->
                    let uu____2994 =
                      let uu____2997 = FStar_Tactics_Types.goal_env g  in
                      let uu____2998 =
                        let uu____2999 =
                          let uu____3002 =
                            let uu____3003 =
                              let uu____3010 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3010)  in
                            FStar_Syntax_Syntax.NT uu____3003  in
                          [uu____3002]  in
                        FStar_Syntax_Subst.subst uu____2999 phi1  in
                      FStar_Tactics_Monad.mk_irrelevant_goal
                        "refine_intro refinement" uu____2997 uu____2998
                        g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    FStar_Tactics_Monad.bind uu____2994
                      (fun g2  ->
                         FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                           (fun uu____3019  ->
                              FStar_Tactics_Monad.add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "refine_intro")
      uu____2890
  
let (__exact_now :
  Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun set_expected_typ1  ->
    fun t  ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3048 = FStar_Tactics_Types.goal_env goal  in
               let uu____3049 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3048 uu____3049
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3052 = __tc env t  in
           FStar_Tactics_Monad.bind uu____3052
             (fun uu____3071  ->
                match uu____3071 with
                | (t1,typ,guard) ->
                    FStar_Tactics_Monad.mlog
                      (fun uu____3086  ->
                         let uu____3087 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3089 =
                           let uu____3091 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3091
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3087 uu____3089)
                      (fun uu____3095  ->
                         let uu____3096 =
                           let uu____3099 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3099 guard  in
                         FStar_Tactics_Monad.bind uu____3096
                           (fun uu____3102  ->
                              FStar_Tactics_Monad.mlog
                                (fun uu____3106  ->
                                   let uu____3107 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3109 =
                                     let uu____3111 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3111
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3107 uu____3109)
                                (fun uu____3115  ->
                                   let uu____3116 =
                                     let uu____3120 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3121 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3120 typ uu____3121  in
                                   FStar_Tactics_Monad.bind uu____3116
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3131 =
                                             let uu____3138 =
                                               let uu____3144 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal
                                                  in
                                               tts uu____3144  in
                                             let uu____3145 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu____3138 typ uu____3145
                                              in
                                           match uu____3131 with
                                           | (typ1,goalt) ->
                                               let uu____3154 =
                                                 let uu____3156 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 tts uu____3156 t1  in
                                               let uu____3157 =
                                                 let uu____3159 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____3160 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal
                                                    in
                                                 tts uu____3159 uu____3160
                                                  in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu____3154 typ1 goalt
                                                 uu____3157)))))))
  
let (t_exact :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3186 =
          FStar_Tactics_Monad.mlog
            (fun uu____3191  ->
               let uu____3192 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3192)
            (fun uu____3197  ->
               let uu____3198 =
                 let uu____3205 = __exact_now set_expected_typ1 tm  in
                 catch uu____3205  in
               FStar_Tactics_Monad.bind uu____3198
                 (fun uu___2_3214  ->
                    match uu___2_3214 with
                    | FStar_Util.Inr r -> FStar_Tactics_Monad.ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        FStar_Tactics_Monad.traise e
                    | FStar_Util.Inl e ->
                        FStar_Tactics_Monad.mlog
                          (fun uu____3225  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3229  ->
                             let uu____3230 =
                               let uu____3237 =
                                 let uu____3240 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 FStar_Tactics_Monad.bind uu____3240
                                   (fun uu____3245  ->
                                      let uu____3246 = refine_intro ()  in
                                      FStar_Tactics_Monad.bind uu____3246
                                        (fun uu____3250  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____3237  in
                             FStar_Tactics_Monad.bind uu____3230
                               (fun uu___1_3257  ->
                                  match uu___1_3257 with
                                  | FStar_Util.Inr r ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3266  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____3269  ->
                                           FStar_Tactics_Monad.ret ())
                                  | FStar_Util.Inl uu____3270 ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3272  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____3275  ->
                                           FStar_Tactics_Monad.traise e)))))
           in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "exact") uu____3186
  
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
            let uu____3376 = f e ty2 ty1  in
            FStar_Tactics_Monad.bind uu____3376
              (fun uu___3_3390  ->
                 if uu___3_3390
                 then FStar_Tactics_Monad.ret acc
                 else
                   (let uu____3410 = FStar_Syntax_Util.arrow_one ty1  in
                    match uu____3410 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____3431 =
                          FStar_Syntax_Print.term_to_string ty1  in
                        let uu____3433 =
                          FStar_Syntax_Print.term_to_string ty2  in
                        fail2 "Could not instantiate, %s to %s" uu____3431
                          uu____3433
                    | FStar_Pervasives_Native.Some (b,c) ->
                        let uu____3450 =
                          let uu____3452 = FStar_Syntax_Util.is_total_comp c
                             in
                          Prims.op_Negation uu____3452  in
                        if uu____3450
                        then FStar_Tactics_Monad.fail "Codomain is effectful"
                        else
                          (let uu____3476 =
                             FStar_Tactics_Monad.new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           FStar_Tactics_Monad.bind uu____3476
                             (fun uu____3503  ->
                                match uu____3503 with
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
        let uu____3609 =
          FStar_Tactics_Monad.mlog
            (fun uu____3614  ->
               let uu____3615 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____3615)
            (fun uu____3619  ->
               FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                 (fun goal  ->
                    let e = FStar_Tactics_Types.goal_env goal  in
                    let uu____3625 = __tc e tm  in
                    FStar_Tactics_Monad.bind uu____3625
                      (fun uu____3646  ->
                         match uu____3646 with
                         | (tm1,typ,guard) ->
                             let typ1 = bnorm e typ  in
                             let uu____3659 =
                               let uu____3670 =
                                 FStar_Tactics_Types.goal_type goal  in
                               try_unify_by_application only_match e typ1
                                 uu____3670
                                in
                             FStar_Tactics_Monad.bind uu____3659
                               (fun uvs  ->
                                  FStar_Tactics_Monad.mlog
                                    (fun uu____3691  ->
                                       let uu____3692 =
                                         FStar_Common.string_of_list
                                           (fun uu____3704  ->
                                              match uu____3704 with
                                              | (t,uu____3713,uu____3714) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t) uvs
                                          in
                                       FStar_Util.print1
                                         "t_apply: found args = %s\n"
                                         uu____3692)
                                    (fun uu____3722  ->
                                       let fix_qual q =
                                         match q with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Meta
                                             uu____3737) ->
                                             FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                                  false)
                                         | uu____3741 -> q  in
                                       let w =
                                         FStar_List.fold_right
                                           (fun uu____3764  ->
                                              fun w  ->
                                                match uu____3764 with
                                                | (uvt,q,uu____3782) ->
                                                    FStar_Syntax_Util.mk_app
                                                      w [(uvt, (fix_qual q))])
                                           uvs tm1
                                          in
                                       let uvset =
                                         let uu____3814 =
                                           FStar_Syntax_Free.new_uv_set ()
                                            in
                                         FStar_List.fold_right
                                           (fun uu____3831  ->
                                              fun s  ->
                                                match uu____3831 with
                                                | (uu____3843,uu____3844,uv)
                                                    ->
                                                    let uu____3846 =
                                                      FStar_Syntax_Free.uvars
                                                        uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                       in
                                                    FStar_Util.set_union s
                                                      uu____3846) uvs
                                           uu____3814
                                          in
                                       let free_in_some_goal uv =
                                         FStar_Util.set_mem uv uvset  in
                                       let uu____3856 = solve' goal w  in
                                       FStar_Tactics_Monad.bind uu____3856
                                         (fun uu____3861  ->
                                            let uu____3862 =
                                              FStar_Tactics_Monad.mapM
                                                (fun uu____3879  ->
                                                   match uu____3879 with
                                                   | (uvt,q,uv) ->
                                                       let uu____3891 =
                                                         FStar_Syntax_Unionfind.find
                                                           uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                          in
                                                       (match uu____3891 with
                                                        | FStar_Pervasives_Native.Some
                                                            uu____3896 ->
                                                            FStar_Tactics_Monad.ret
                                                              ()
                                                        | FStar_Pervasives_Native.None
                                                             ->
                                                            let uu____3897 =
                                                              uopt &&
                                                                (free_in_some_goal
                                                                   uv)
                                                               in
                                                            if uu____3897
                                                            then
                                                              FStar_Tactics_Monad.ret
                                                                ()
                                                            else
                                                              (let uu____3904
                                                                 =
                                                                 let uu____3907
                                                                   =
                                                                   bnorm_goal
                                                                    (let uu___604_3910
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___604_3910.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___604_3910.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___604_3910.FStar_Tactics_Types.label)
                                                                    })
                                                                    in
                                                                 [uu____3907]
                                                                  in
                                                               FStar_Tactics_Monad.add_goals
                                                                 uu____3904)))
                                                uvs
                                               in
                                            FStar_Tactics_Monad.bind
                                              uu____3862
                                              (fun uu____3915  ->
                                                 proc_guard "apply guard" e
                                                   guard)))))))
           in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply") uu____3609
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____3943 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____3943
    then
      let uu____3952 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3967 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4020 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3952 with
      | (pre,post) ->
          let post1 =
            let uu____4053 =
              let uu____4064 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4064]  in
            FStar_Syntax_Util.mk_app post uu____4053  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4095 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4095
       then
         let uu____4104 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4104
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
            let uu____4183 = f x e  in
            FStar_Tactics_Monad.bind uu____4183
              (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun tm  ->
    let uu____4198 =
      let uu____4201 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps  ->
             FStar_Tactics_Monad.mlog
               (fun uu____4208  ->
                  let uu____4209 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4209)
               (fun uu____4214  ->
                  let is_unit_t t =
                    let uu____4222 =
                      let uu____4223 = FStar_Syntax_Subst.compress t  in
                      uu____4223.FStar_Syntax_Syntax.n  in
                    match uu____4222 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4229 -> false  in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                    (fun goal  ->
                       let uu____4234 =
                         let uu____4243 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4243 tm  in
                       FStar_Tactics_Monad.bind uu____4234
                         (fun uu____4258  ->
                            match uu____4258 with
                            | (tm1,t,guard) ->
                                let uu____4270 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4270 with
                                 | (bs,comp) ->
                                     let uu____4279 = lemma_or_sq comp  in
                                     (match uu____4279 with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Tactics_Monad.fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4299 =
                                            fold_left
                                              (fun uu____4361  ->
                                                 fun uu____4362  ->
                                                   match (uu____4361,
                                                           uu____4362)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____4513 =
                                                         is_unit_t b_t  in
                                                       if uu____4513
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
                                                         (let uu____4636 =
                                                            let uu____4643 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_Tactics_Monad.new_uvar
                                                              "apply_lemma"
                                                              uu____4643 b_t
                                                             in
                                                          FStar_Tactics_Monad.bind
                                                            uu____4636
                                                            (fun uu____4674 
                                                               ->
                                                               match uu____4674
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
                                          FStar_Tactics_Monad.bind uu____4299
                                            (fun uu____4860  ->
                                               match uu____4860 with
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
                                                   let uu____4948 =
                                                     let uu____4952 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____4953 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____4954 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____4952
                                                       uu____4953 uu____4954
                                                      in
                                                   FStar_Tactics_Monad.bind
                                                     uu____4948
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____4966 =
                                                            let uu____4973 =
                                                              let uu____4979
                                                                =
                                                                FStar_Tactics_Types.goal_env
                                                                  goal
                                                                 in
                                                              tts uu____4979
                                                               in
                                                            let uu____4980 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            let uu____4981 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Err.print_discrepancy
                                                              uu____4973
                                                              uu____4980
                                                              uu____4981
                                                             in
                                                          match uu____4966
                                                          with
                                                          | (post2,goalt) ->
                                                              let uu____4990
                                                                =
                                                                let uu____4992
                                                                  =
                                                                  FStar_Tactics_Types.goal_env
                                                                    goal
                                                                   in
                                                                tts
                                                                  uu____4992
                                                                  tm1
                                                                 in
                                                              fail3
                                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                uu____4990
                                                                post2 goalt
                                                        else
                                                          (let uu____4996 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           FStar_Tactics_Monad.bind
                                                             uu____4996
                                                             (fun uu____5004 
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____5030
                                                                    =
                                                                    let uu____5033
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5033
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5030
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
                                                                    let uu____5069
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5069)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____5086
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____5086
                                                                  with
                                                                  | (hd1,uu____5105)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5132)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5149
                                                                    -> false)
                                                                   in
                                                                let uu____5151
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    implicits1
                                                                    (
                                                                    FStar_Tactics_Monad.mapM
                                                                    (fun imp 
                                                                    ->
                                                                    let uu____5192
                                                                    = imp  in
                                                                    match uu____5192
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____5203
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5203
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5225)
                                                                    ->
                                                                    let uu____5250
                                                                    =
                                                                    let uu____5251
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5251.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5250
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5259)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___721_5279
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___721_5279.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___721_5279.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___721_5279.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___721_5279.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    FStar_Tactics_Monad.ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5282
                                                                    ->
                                                                    FStar_Tactics_Monad.mlog
                                                                    (fun
                                                                    uu____5288
                                                                     ->
                                                                    let uu____5289
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5291
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5289
                                                                    uu____5291)
                                                                    (fun
                                                                    uu____5297
                                                                     ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____5299
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true
                                                                    uu____5299
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5301
                                                                    =
                                                                    let uu____5304
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5308
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5310
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5308
                                                                    uu____5310
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5316
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5304
                                                                    uu____5316
                                                                    g_typ  in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5301
                                                                    (fun
                                                                    uu____5320
                                                                     ->
                                                                    FStar_Tactics_Monad.ret
                                                                    []))))))
                                                                   in
                                                                FStar_Tactics_Monad.bind
                                                                  uu____5151
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
                                                                    let uu____5384
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5384
                                                                    then
                                                                    let uu____5389
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5389
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
                                                                    let uu____5404
                                                                    =
                                                                    let uu____5406
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5406
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5404)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5407
                                                                    =
                                                                    let uu____5410
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5410
                                                                    guard  in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5407
                                                                    (fun
                                                                    uu____5414
                                                                     ->
                                                                    let uu____5415
                                                                    =
                                                                    let uu____5418
                                                                    =
                                                                    let uu____5420
                                                                    =
                                                                    let uu____5422
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5423
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5422
                                                                    uu____5423
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5420
                                                                     in
                                                                    if
                                                                    uu____5418
                                                                    then
                                                                    let uu____5427
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    FStar_Tactics_Monad.add_irrelevant_goal
                                                                    goal
                                                                    "apply_lemma precondition"
                                                                    uu____5427
                                                                    pre1
                                                                    else
                                                                    FStar_Tactics_Monad.ret
                                                                    ()  in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5415
                                                                    (fun
                                                                    uu____5432
                                                                     ->
                                                                    FStar_Tactics_Monad.add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____4201  in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply_lemma")
      uu____4198
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5456 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5456 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5466::(e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5526::uu____5527::(e1,uu____5529)::(e2,uu____5531)::[]))
        when FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5608 ->
        let uu____5611 = FStar_Syntax_Util.unb2t typ  in
        (match uu____5611 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____5625 = FStar_Syntax_Util.head_and_args t  in
             (match uu____5625 with
              | (hd1,args) ->
                  let uu____5674 =
                    let uu____5689 =
                      let uu____5690 = FStar_Syntax_Subst.compress hd1  in
                      uu____5690.FStar_Syntax_Syntax.n  in
                    (uu____5689, args)  in
                  (match uu____5674 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(uu____5710,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____5711))::
                      (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                           )::[])
                       when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____5779 -> FStar_Pervasives_Native.None)))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5816 = destruct_eq' typ  in
    match uu____5816 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5846 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5846 with
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
        let uu____5915 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5915 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____5973 = aux e'  in
               FStar_Util.map_opt uu____5973
                 (fun uu____6004  ->
                    match uu____6004 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____6030 = aux e  in
      FStar_Util.map_opt uu____6030
        (fun uu____6061  ->
           match uu____6061 with
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
        let uu____6138 =
          let uu____6149 = FStar_Tactics_Types.goal_env g  in
          split_env b1 uu____6149  in
        match uu____6138 with
        | FStar_Pervasives_Native.Some (e0,b11,bvs) ->
            let bs =
              FStar_List.map FStar_Syntax_Syntax.mk_binder (b11 :: bvs)  in
            let t = FStar_Tactics_Types.goal_type g  in
            let uu____6189 =
              let uu____6202 = FStar_Syntax_Subst.close_binders bs  in
              let uu____6211 = FStar_Syntax_Subst.close bs t  in
              (uu____6202, uu____6211)  in
            (match uu____6189 with
             | (bs',t') ->
                 let bs'1 =
                   let uu____6255 = FStar_Syntax_Syntax.mk_binder b2  in
                   let uu____6262 = FStar_List.tail bs'  in uu____6255 ::
                     uu____6262
                    in
                 let uu____6283 = FStar_Syntax_Subst.open_term bs'1 t'  in
                 (match uu____6283 with
                  | (bs'',t'') ->
                      let b21 =
                        let uu____6299 = FStar_List.hd bs''  in
                        FStar_Pervasives_Native.fst uu____6299  in
                      let new_env =
                        let uu____6315 =
                          FStar_List.map FStar_Pervasives_Native.fst bs''  in
                        push_bvs e0 uu____6315  in
                      let uu____6326 =
                        FStar_Tactics_Monad.new_uvar "subst_goal" new_env t''
                         in
                      FStar_Tactics_Monad.bind uu____6326
                        (fun uu____6350  ->
                           match uu____6350 with
                           | (uvt,uv) ->
                               let goal' =
                                 FStar_Tactics_Types.mk_goal new_env uv
                                   g.FStar_Tactics_Types.opts
                                   g.FStar_Tactics_Types.is_guard
                                   g.FStar_Tactics_Types.label
                                  in
                               let sol =
                                 let uu____6369 =
                                   FStar_Syntax_Util.abs bs'' uvt
                                     FStar_Pervasives_Native.None
                                    in
                                 let uu____6372 =
                                   FStar_List.map
                                     (fun uu____6393  ->
                                        match uu____6393 with
                                        | (bv,q) ->
                                            let uu____6406 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                bv
                                               in
                                            FStar_Syntax_Syntax.as_arg
                                              uu____6406) bs
                                    in
                                 FStar_Syntax_Util.mk_app uu____6369
                                   uu____6372
                                  in
                               let uu____6407 = set_solution g sol  in
                               FStar_Tactics_Monad.bind uu____6407
                                 (fun uu____6417  ->
                                    FStar_Tactics_Monad.ret
                                      (FStar_Pervasives_Native.Some
                                         (b21, goal'))))))
        | FStar_Pervasives_Native.None  ->
            FStar_Tactics_Monad.ret FStar_Pervasives_Native.None
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun h  ->
    let uu____6456 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal  ->
           let uu____6464 = h  in
           match uu____6464 with
           | (bv,uu____6468) ->
               FStar_Tactics_Monad.mlog
                 (fun uu____6476  ->
                    let uu____6477 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____6479 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6477
                      uu____6479)
                 (fun uu____6484  ->
                    let uu____6485 =
                      let uu____6496 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____6496  in
                    match uu____6485 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Tactics_Monad.fail
                          "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____6523 =
                          let uu____6530 =
                            whnf e0 bv1.FStar_Syntax_Syntax.sort  in
                          destruct_eq uu____6530  in
                        (match uu____6523 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6539 =
                               let uu____6540 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6540.FStar_Syntax_Syntax.n  in
                             (match uu____6539 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let t = FStar_Tactics_Types.goal_type goal
                                     in
                                  let bs =
                                    FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder bvs
                                     in
                                  let uu____6567 =
                                    let uu____6572 =
                                      FStar_Syntax_Subst.close_binders bs  in
                                    let uu____6573 =
                                      FStar_Syntax_Subst.close bs t  in
                                    (uu____6572, uu____6573)  in
                                  (match uu____6567 with
                                   | (bs',t') ->
                                       let uu____6578 =
                                         let uu____6583 =
                                           FStar_Syntax_Subst.subst_binders s
                                             bs'
                                            in
                                         let uu____6584 =
                                           FStar_Syntax_Subst.subst s t  in
                                         (uu____6583, uu____6584)  in
                                       (match uu____6578 with
                                        | (bs'1,t'1) ->
                                            let uu____6589 =
                                              FStar_Syntax_Subst.open_term
                                                bs'1 t'1
                                               in
                                            (match uu____6589 with
                                             | (bs'',t'') ->
                                                 let new_env =
                                                   let uu____6599 =
                                                     let uu____6602 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         bs''
                                                        in
                                                     bv1 :: uu____6602  in
                                                   push_bvs e0 uu____6599  in
                                                 let uu____6613 =
                                                   FStar_Tactics_Monad.new_uvar
                                                     "rewrite" new_env t''
                                                    in
                                                 FStar_Tactics_Monad.bind
                                                   uu____6613
                                                   (fun uu____6631  ->
                                                      match uu____6631 with
                                                      | (uvt,uv) ->
                                                          let goal' =
                                                            FStar_Tactics_Types.mk_goal
                                                              new_env uv
                                                              goal.FStar_Tactics_Types.opts
                                                              goal.FStar_Tactics_Types.is_guard
                                                              goal.FStar_Tactics_Types.label
                                                             in
                                                          let sol =
                                                            let uu____6644 =
                                                              FStar_Syntax_Util.abs
                                                                bs'' uvt
                                                                FStar_Pervasives_Native.None
                                                               in
                                                            let uu____6647 =
                                                              FStar_List.map
                                                                (fun
                                                                   uu____6668
                                                                    ->
                                                                   match uu____6668
                                                                   with
                                                                   | 
                                                                   (bv2,uu____6676)
                                                                    ->
                                                                    let uu____6681
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv2  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____6681)
                                                                bs
                                                               in
                                                            FStar_Syntax_Util.mk_app
                                                              uu____6644
                                                              uu____6647
                                                             in
                                                          let uu____6682 =
                                                            set_solution goal
                                                              sol
                                                             in
                                                          FStar_Tactics_Monad.bind
                                                            uu____6682
                                                            (fun uu____6686 
                                                               ->
                                                               FStar_Tactics_Monad.replace_cur
                                                                 goal')))))
                              | uu____6687 ->
                                  FStar_Tactics_Monad.fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6689 ->
                             FStar_Tactics_Monad.fail
                               "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rewrite") uu____6456
  
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac)
  =
  fun b  ->
    fun s  ->
      let uu____6719 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal  ->
             let uu____6741 = b  in
             match uu____6741 with
             | (bv,q) ->
                 let bv' =
                   let uu____6757 =
                     let uu___899_6758 = bv  in
                     let uu____6759 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6759;
                       FStar_Syntax_Syntax.index =
                         (uu___899_6758.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___899_6758.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6757  in
                 let uu____6761 = subst_goal bv bv' goal  in
                 FStar_Tactics_Monad.bind uu____6761
                   (fun uu___4_6783  ->
                      match uu___4_6783 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Tactics_Monad.fail
                            "binder not found in environment"
                      | FStar_Pervasives_Native.Some (bv'1,goal1) ->
                          let uu____6815 =
                            FStar_Tactics_Monad.replace_cur goal1  in
                          FStar_Tactics_Monad.bind uu____6815
                            (fun uu____6825  ->
                               FStar_Tactics_Monad.ret (bv'1, q))))
         in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rename_to")
        uu____6719
  
let (binder_retype :
  FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b  ->
    let uu____6861 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal  ->
           let uu____6870 = b  in
           match uu____6870 with
           | (bv,uu____6874) ->
               let uu____6879 =
                 let uu____6890 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6890  in
               (match uu____6879 with
                | FStar_Pervasives_Native.None  ->
                    FStar_Tactics_Monad.fail
                      "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____6917 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6917 with
                     | (ty,u) ->
                         let uu____6926 =
                           FStar_Tactics_Monad.new_uvar "binder_retype" e0 ty
                            in
                         FStar_Tactics_Monad.bind uu____6926
                           (fun uu____6945  ->
                              match uu____6945 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___926_6955 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___926_6955.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___926_6955.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6959 =
                                      let uu____6960 =
                                        let uu____6967 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____6967)  in
                                      FStar_Syntax_Syntax.NT uu____6960  in
                                    [uu____6959]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___931_6979 = b1  in
                                         let uu____6980 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___931_6979.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___931_6979.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6980
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  FStar_Tactics_Monad.bind
                                    FStar_Tactics_Monad.dismiss
                                    (fun uu____6987  ->
                                       let new_goal =
                                         let uu____6989 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6990 =
                                           let uu____6991 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6991
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6989 uu____6990
                                          in
                                       let uu____6992 =
                                         FStar_Tactics_Monad.add_goals
                                           [new_goal]
                                          in
                                       FStar_Tactics_Monad.bind uu____6992
                                         (fun uu____6997  ->
                                            let uu____6998 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            FStar_Tactics_Monad.add_irrelevant_goal
                                              goal "binder_retype equation"
                                              e0 uu____6998))))))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "binder_retype")
      uu____6861
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac)
  =
  fun s  ->
    fun b  ->
      let uu____7024 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal  ->
             let uu____7033 = b  in
             match uu____7033 with
             | (bv,uu____7037) ->
                 let uu____7042 =
                   let uu____7053 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____7053  in
                 (match uu____7042 with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Tactics_Monad.fail
                        "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____7083 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____7083
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___952_7088 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___952_7088.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___952_7088.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____7090 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      FStar_Tactics_Monad.replace_cur uu____7090))
         in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_binder_type")
        uu____7024
  
let (revert : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7103  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal  ->
         let uu____7109 =
           let uu____7116 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____7116  in
         match uu____7109 with
         | FStar_Pervasives_Native.None  ->
             FStar_Tactics_Monad.fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____7133 =
                 let uu____7136 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____7136  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____7133
                in
             let uu____7151 = FStar_Tactics_Monad.new_uvar "revert" env' typ'
                in
             FStar_Tactics_Monad.bind uu____7151
               (fun uu____7167  ->
                  match uu____7167 with
                  | (r,u_r) ->
                      let uu____7176 =
                        let uu____7179 =
                          let uu____7180 =
                            let uu____7181 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____7181.FStar_Syntax_Syntax.pos  in
                          let uu____7184 =
                            let uu____7189 =
                              let uu____7190 =
                                let uu____7199 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____7199  in
                              [uu____7190]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____7189  in
                          uu____7184 FStar_Pervasives_Native.None uu____7180
                           in
                        set_solution goal uu____7179  in
                      FStar_Tactics_Monad.bind uu____7176
                        (fun uu____7218  ->
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
      let uu____7232 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____7232
  
let (clear : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal  ->
         FStar_Tactics_Monad.mlog
           (fun uu____7253  ->
              let uu____7254 = FStar_Syntax_Print.binder_to_string b  in
              let uu____7256 =
                let uu____7258 =
                  let uu____7260 =
                    let uu____7269 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____7269  in
                  FStar_All.pipe_right uu____7260 FStar_List.length  in
                FStar_All.pipe_right uu____7258 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____7254 uu____7256)
           (fun uu____7290  ->
              let uu____7291 =
                let uu____7302 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____7302  in
              match uu____7291 with
              | FStar_Pervasives_Native.None  ->
                  FStar_Tactics_Monad.fail
                    "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> FStar_Tactics_Monad.ret ()
                    | bv'::bvs2 ->
                        let uu____7347 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____7347
                        then
                          let uu____7352 =
                            let uu____7354 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____7354
                             in
                          FStar_Tactics_Monad.fail uu____7352
                        else check1 bvs2
                     in
                  let uu____7359 =
                    let uu____7361 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____7361  in
                  if uu____7359
                  then
                    FStar_Tactics_Monad.fail
                      "Cannot clear; binder present in goal"
                  else
                    (let uu____7368 = check1 bvs  in
                     FStar_Tactics_Monad.bind uu____7368
                       (fun uu____7374  ->
                          let env' = push_bvs e' bvs  in
                          let uu____7376 =
                            let uu____7383 =
                              FStar_Tactics_Types.goal_type goal  in
                            FStar_Tactics_Monad.new_uvar "clear.witness" env'
                              uu____7383
                             in
                          FStar_Tactics_Monad.bind uu____7376
                            (fun uu____7393  ->
                               match uu____7393 with
                               | (ut,uvar_ut) ->
                                   let uu____7402 = set_solution goal ut  in
                                   FStar_Tactics_Monad.bind uu____7402
                                     (fun uu____7407  ->
                                        let uu____7408 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        FStar_Tactics_Monad.replace_cur
                                          uu____7408))))))
  
let (clear_top : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7416  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal  ->
         let uu____7422 =
           let uu____7429 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____7429  in
         match uu____7422 with
         | FStar_Pervasives_Native.None  ->
             FStar_Tactics_Monad.fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____7438) ->
             let uu____7443 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____7443)
  
let (prune : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____7463 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____7463  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         FStar_Tactics_Monad.replace_cur g')
  
let (addns : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____7484 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____7484  in
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
           let uu____7504 =
             let uu____7508 = FStar_Tactics_Types.goal_env g  in
             do_unify uu____7508 l r  in
           FStar_Tactics_Monad.bind uu____7504
             (fun b  ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____7519 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7519 l
                      in
                   let r1 =
                     let uu____7521 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7521 r
                      in
                   let uu____7522 =
                     let uu____7526 = FStar_Tactics_Types.goal_env g  in
                     do_unify uu____7526 l1 r1  in
                   FStar_Tactics_Monad.bind uu____7522
                     (fun b1  ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____7536 =
                             let uu____7543 =
                               let uu____7549 =
                                 FStar_Tactics_Types.goal_env g  in
                               tts uu____7549  in
                             FStar_TypeChecker_Err.print_discrepancy
                               uu____7543 l1 r1
                              in
                           match uu____7536 with
                           | (ls,rs) ->
                               fail2 "not a trivial equality ((%s) vs (%s))"
                                 ls rs)))))
  
let (trefl : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7566  ->
    let uu____7569 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g  ->
           let uu____7577 =
             let uu____7584 =
               let uu____7585 = FStar_Tactics_Types.goal_env g  in
               let uu____7586 = FStar_Tactics_Types.goal_type g  in
               whnf uu____7585 uu____7586  in
             destruct_eq uu____7584  in
           match uu____7577 with
           | FStar_Pervasives_Native.Some (l,r) -> _trefl l r
           | FStar_Pervasives_Native.None  ->
               let uu____7599 =
                 let uu____7601 = FStar_Tactics_Types.goal_env g  in
                 let uu____7602 = FStar_Tactics_Types.goal_type g  in
                 tts uu____7601 uu____7602  in
               fail1 "not an equality (%s)" uu____7599)
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "trefl") uu____7569
  
let (dup : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7616  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g  ->
         let env = FStar_Tactics_Types.goal_env g  in
         let uu____7624 =
           let uu____7631 = FStar_Tactics_Types.goal_type g  in
           FStar_Tactics_Monad.new_uvar "dup" env uu____7631  in
         FStar_Tactics_Monad.bind uu____7624
           (fun uu____7641  ->
              match uu____7641 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1038_7651 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1038_7651.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1038_7651.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1038_7651.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1038_7651.FStar_Tactics_Types.label)
                    }  in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____7655  ->
                       let t_eq =
                         let uu____7657 =
                           let uu____7658 = FStar_Tactics_Types.goal_type g
                              in
                           env.FStar_TypeChecker_Env.universe_of env
                             uu____7658
                            in
                         let uu____7659 = FStar_Tactics_Types.goal_type g  in
                         let uu____7660 = FStar_Tactics_Types.goal_witness g
                            in
                         FStar_Syntax_Util.mk_eq2 uu____7657 uu____7659 u
                           uu____7660
                          in
                       let uu____7661 =
                         FStar_Tactics_Monad.add_irrelevant_goal g
                           "dup equation" env t_eq
                          in
                       FStar_Tactics_Monad.bind uu____7661
                         (fun uu____7667  ->
                            let uu____7668 =
                              FStar_Tactics_Monad.add_goals [g']  in
                            FStar_Tactics_Monad.bind uu____7668
                              (fun uu____7672  -> FStar_Tactics_Monad.ret ())))))
  
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
              let uu____7798 = f x y  in
              if uu____7798 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____7821 -> (acc, l11, l21)  in
        let uu____7836 = aux [] l1 l2  in
        match uu____7836 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____7942 = get_phi g1  in
      match uu____7942 with
      | FStar_Pervasives_Native.None  ->
          FStar_Tactics_Monad.fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____7949 = get_phi g2  in
          (match uu____7949 with
           | FStar_Pervasives_Native.None  ->
               FStar_Tactics_Monad.fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____7962 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____7962 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____7993 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____7993 phi1  in
                    let t2 =
                      let uu____8003 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____8003 phi2  in
                    let uu____8012 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    FStar_Tactics_Monad.bind uu____8012
                      (fun uu____8017  ->
                         let uu____8018 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         FStar_Tactics_Monad.bind uu____8018
                           (fun uu____8025  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1090_8030 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____8031 =
                                  FStar_Util.smap_create (Prims.of_int (100))
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1090_8030.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1090_8030.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1090_8030.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1090_8030.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____8031;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1090_8030.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1090_8030.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1090_8030.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1090_8030.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1090_8030.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1090_8030.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1090_8030.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1090_8030.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1090_8030.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1090_8030.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1090_8030.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1090_8030.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1090_8030.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1090_8030.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1090_8030.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1090_8030.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1090_8030.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1090_8030.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1090_8030.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1090_8030.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1090_8030.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1090_8030.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1090_8030.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1090_8030.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1090_8030.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1090_8030.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1090_8030.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1090_8030.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1090_8030.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1090_8030.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1090_8030.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1090_8030.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1090_8030.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1090_8030.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1090_8030.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1090_8030.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1090_8030.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1090_8030.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1090_8030.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1090_8030.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1090_8030.FStar_TypeChecker_Env.erasable_types_tab)
                                }  in
                              let uu____8035 =
                                FStar_Tactics_Monad.mk_irrelevant_goal
                                  "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              FStar_Tactics_Monad.bind uu____8035
                                (fun goal  ->
                                   FStar_Tactics_Monad.mlog
                                     (fun uu____8045  ->
                                        let uu____8046 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g1
                                           in
                                        let uu____8048 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g2
                                           in
                                        let uu____8050 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            goal
                                           in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____8046 uu____8048 uu____8050)
                                     (fun uu____8054  ->
                                        FStar_Tactics_Monad.ret goal))))))
  
let (join : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____8062  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____8078 =
               FStar_Tactics_Monad.set
                 (let uu___1105_8083 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1105_8083.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1105_8083.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1105_8083.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1105_8083.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1105_8083.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1105_8083.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1105_8083.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1105_8083.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1105_8083.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1105_8083.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1105_8083.FStar_Tactics_Types.local_state)
                  })
                in
             FStar_Tactics_Monad.bind uu____8078
               (fun uu____8086  ->
                  let uu____8087 = join_goals g1 g2  in
                  FStar_Tactics_Monad.bind uu____8087
                    (fun g12  -> FStar_Tactics_Monad.add_goals [g12]))
         | uu____8092 -> FStar_Tactics_Monad.fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s  ->
    let uu____8108 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g  ->
           FStar_Options.push ();
           (let uu____8121 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____8121);
           (let res = FStar_Options.set_options s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1116_8128 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1116_8128.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1116_8128.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1116_8128.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1116_8128.FStar_Tactics_Types.label)
                   }  in
                 FStar_Tactics_Monad.replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "set_options")
      uu____8108
  
let (top_env : unit -> env FStar_Tactics_Monad.tac) =
  fun uu____8145  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps  ->
         FStar_All.pipe_left FStar_Tactics_Monad.ret
           ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____8160  ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g  ->
         let uu____8168 =
           (FStar_Options.lax ()) ||
             (let uu____8171 = FStar_Tactics_Types.goal_env g  in
              uu____8171.FStar_TypeChecker_Env.lax)
            in
         FStar_Tactics_Monad.ret uu____8168)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8188 =
        FStar_Tactics_Monad.mlog
          (fun uu____8193  ->
             let uu____8194 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____8194)
          (fun uu____8198  ->
             FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
               (fun goal  ->
                  let env =
                    let uu____8204 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____8204 ty  in
                  let uu____8205 = __tc_ghost env tm  in
                  FStar_Tactics_Monad.bind uu____8205
                    (fun uu____8224  ->
                       match uu____8224 with
                       | (tm1,typ,guard) ->
                           FStar_Tactics_Monad.mlog
                             (fun uu____8238  ->
                                let uu____8239 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____8239)
                             (fun uu____8243  ->
                                FStar_Tactics_Monad.mlog
                                  (fun uu____8246  ->
                                     let uu____8247 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____8247)
                                  (fun uu____8252  ->
                                     let uu____8253 =
                                       proc_guard "unquote" env guard  in
                                     FStar_Tactics_Monad.bind uu____8253
                                       (fun uu____8258  ->
                                          FStar_Tactics_Monad.ret tm1))))))
         in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unquote") uu____8188
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8283 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> FStar_Tactics_Monad.ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8289 =
              let uu____8296 =
                let uu____8297 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8297
                 in
              FStar_Tactics_Monad.new_uvar "uvar_env.2" env uu____8296  in
            FStar_Tactics_Monad.bind uu____8289
              (fun uu____8314  ->
                 match uu____8314 with
                 | (typ,uvar_typ) -> FStar_Tactics_Monad.ret typ)
         in
      FStar_Tactics_Monad.bind uu____8283
        (fun typ  ->
           let uu____8326 = FStar_Tactics_Monad.new_uvar "uvar_env" env typ
              in
           FStar_Tactics_Monad.bind uu____8326
             (fun uu____8341  ->
                match uu____8341 with
                | (t,uvar_t) -> FStar_Tactics_Monad.ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t  ->
    let uu____8360 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8379 -> g.FStar_Tactics_Types.opts
             | uu____8382 -> FStar_Options.peek ()  in
           let uu____8385 = FStar_Syntax_Util.head_and_args t  in
           match uu____8385 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____8405);
                FStar_Syntax_Syntax.pos = uu____8406;
                FStar_Syntax_Syntax.vars = uu____8407;_},uu____8408)
               ->
               let env1 =
                 let uu___1170_8450 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1170_8450.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1170_8450.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1170_8450.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1170_8450.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1170_8450.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1170_8450.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1170_8450.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1170_8450.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1170_8450.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1170_8450.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1170_8450.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1170_8450.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1170_8450.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1170_8450.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1170_8450.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1170_8450.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___1170_8450.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1170_8450.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1170_8450.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1170_8450.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1170_8450.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1170_8450.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1170_8450.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1170_8450.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1170_8450.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1170_8450.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1170_8450.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1170_8450.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1170_8450.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1170_8450.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1170_8450.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1170_8450.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1170_8450.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1170_8450.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1170_8450.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___1170_8450.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1170_8450.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1170_8450.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1170_8450.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1170_8450.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1170_8450.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1170_8450.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1170_8450.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1170_8450.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1170_8450.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1170_8450.FStar_TypeChecker_Env.erasable_types_tab)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____8454 =
                 let uu____8457 = bnorm_goal g  in [uu____8457]  in
               FStar_Tactics_Monad.add_goals uu____8454
           | uu____8458 -> FStar_Tactics_Monad.fail "not a uvar")
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unshelve") uu____8360
  
let (tac_and :
  Prims.bool FStar_Tactics_Monad.tac ->
    Prims.bool FStar_Tactics_Monad.tac -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun t1  ->
    fun t2  ->
      let comp =
        FStar_Tactics_Monad.bind t1
          (fun b  ->
             let uu____8520 = if b then t2 else FStar_Tactics_Monad.ret false
                in
             FStar_Tactics_Monad.bind uu____8520
               (fun b'  ->
                  if b'
                  then FStar_Tactics_Monad.ret b'
                  else FStar_Tactics_Monad.fail ""))
         in
      let uu____8546 = trytac comp  in
      FStar_Tactics_Monad.bind uu____8546
        (fun uu___5_8558  ->
           match uu___5_8558 with
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
        let uu____8600 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps  ->
               let uu____8608 = __tc e t1  in
               FStar_Tactics_Monad.bind uu____8608
                 (fun uu____8629  ->
                    match uu____8629 with
                    | (t11,ty1,g1) ->
                        let uu____8642 = __tc e t2  in
                        FStar_Tactics_Monad.bind uu____8642
                          (fun uu____8663  ->
                             match uu____8663 with
                             | (t21,ty2,g2) ->
                                 let uu____8676 =
                                   proc_guard "unify_env g1" e g1  in
                                 FStar_Tactics_Monad.bind uu____8676
                                   (fun uu____8683  ->
                                      let uu____8684 =
                                        proc_guard "unify_env g2" e g2  in
                                      FStar_Tactics_Monad.bind uu____8684
                                        (fun uu____8692  ->
                                           let uu____8693 =
                                             do_unify e ty1 ty2  in
                                           let uu____8697 =
                                             do_unify e t11 t21  in
                                           tac_and uu____8693 uu____8697)))))
           in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unify_env")
          uu____8600
  
let (launch_process :
  Prims.string ->
    Prims.string Prims.list ->
      Prims.string -> Prims.string FStar_Tactics_Monad.tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____8745  ->
             let uu____8746 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8746
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
        (fun uu____8780  ->
           let uu____8781 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           FStar_Tactics_Monad.ret uu____8781)
  
let (change : FStar_Reflection_Data.typ -> unit FStar_Tactics_Monad.tac) =
  fun ty  ->
    let uu____8792 =
      FStar_Tactics_Monad.mlog
        (fun uu____8797  ->
           let uu____8798 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8798)
        (fun uu____8802  ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g  ->
                let uu____8806 =
                  let uu____8815 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____8815 ty  in
                FStar_Tactics_Monad.bind uu____8806
                  (fun uu____8827  ->
                     match uu____8827 with
                     | (ty1,uu____8837,guard) ->
                         let uu____8839 =
                           let uu____8842 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____8842 guard  in
                         FStar_Tactics_Monad.bind uu____8839
                           (fun uu____8846  ->
                              let uu____8847 =
                                let uu____8851 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____8852 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____8851 uu____8852 ty1  in
                              FStar_Tactics_Monad.bind uu____8847
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____8861 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     FStar_Tactics_Monad.replace_cur
                                       uu____8861
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____8868 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____8869 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____8868 uu____8869
                                         in
                                      let nty =
                                        let uu____8871 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____8871 ty1  in
                                      let uu____8872 =
                                        let uu____8876 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____8876 ng nty  in
                                      FStar_Tactics_Monad.bind uu____8872
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____8885 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             FStar_Tactics_Monad.replace_cur
                                               uu____8885
                                           else
                                             FStar_Tactics_Monad.fail
                                               "not convertible")))))))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "change") uu____8792
  
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
    let uu____8959 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g  ->
           let uu____8977 =
             let uu____8986 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8986 s_tm  in
           FStar_Tactics_Monad.bind uu____8977
             (fun uu____9004  ->
                match uu____9004 with
                | (s_tm1,s_ty,guard) ->
                    let uu____9022 =
                      let uu____9025 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____9025 guard  in
                    FStar_Tactics_Monad.bind uu____9022
                      (fun uu____9039  ->
                         let s_ty1 =
                           let uu____9041 = FStar_Tactics_Types.goal_env g
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant] uu____9041
                             s_ty
                            in
                         let uu____9042 =
                           FStar_Syntax_Util.head_and_args' s_ty1  in
                         match uu____9042 with
                         | (h,args) ->
                             let uu____9087 =
                               let uu____9094 =
                                 let uu____9095 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____9095.FStar_Syntax_Syntax.n  in
                               match uu____9094 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   FStar_Tactics_Monad.ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____9110;
                                      FStar_Syntax_Syntax.vars = uu____9111;_},us)
                                   -> FStar_Tactics_Monad.ret (fv, us)
                               | uu____9121 ->
                                   FStar_Tactics_Monad.fail
                                     "type is not an fv"
                                in
                             FStar_Tactics_Monad.bind uu____9087
                               (fun uu____9142  ->
                                  match uu____9142 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____9158 =
                                        let uu____9161 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____9161 t_lid
                                         in
                                      (match uu____9158 with
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
                                                let uu____9202 =
                                                  erasable &&
                                                    (let uu____9205 =
                                                       is_irrelevant g  in
                                                     Prims.op_Negation
                                                       uu____9205)
                                                   in
                                                failwhen uu____9202
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____9215  ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____9228  ->
                                                          let uu____9229 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty
                                                             in
                                                          match uu____9229
                                                          with
                                                          | (t_ps1,t_ty1) ->
                                                              let uu____9244
                                                                =
                                                                FStar_Tactics_Monad.mapM
                                                                  (fun c_lid 
                                                                    ->
                                                                    let uu____9272
                                                                    =
                                                                    let uu____9275
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____9275
                                                                    c_lid  in
                                                                    match uu____9272
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
                                                                    uu____9352
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
                                                                    let uu____9357
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____9357
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____9380
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____9380
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____9399
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname
                                                                     in
                                                                    let ppname1
                                                                    =
                                                                    let uu___1297_9422
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
                                                                    (uu___1297_9422.FStar_Ident.idRange)
                                                                    }  in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    (let uu___1300_9426
                                                                    = bv  in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1300_9426.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (uu___1300_9426.FStar_Syntax_Syntax.sort)
                                                                    })  in
                                                                    let bs' =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9452
                                                                     ->
                                                                    match uu____9452
                                                                    with
                                                                    | 
                                                                    (bv,aq)
                                                                    ->
                                                                    let uu____9471
                                                                    =
                                                                    rename_bv
                                                                    bv  in
                                                                    (uu____9471,
                                                                    aq)) bs
                                                                     in
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun
                                                                    uu____9496
                                                                     ->
                                                                    fun
                                                                    uu____9497
                                                                     ->
                                                                    match 
                                                                    (uu____9496,
                                                                    uu____9497)
                                                                    with
                                                                    | 
                                                                    ((bv,uu____9523),
                                                                    (bv',uu____9525))
                                                                    ->
                                                                    let uu____9546
                                                                    =
                                                                    let uu____9553
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv'  in
                                                                    (bv,
                                                                    uu____9553)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____9546)
                                                                    bs bs'
                                                                     in
                                                                    let uu____9558
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs'  in
                                                                    let uu____9567
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst1
                                                                    comp  in
                                                                    (uu____9558,
                                                                    uu____9567)
                                                                     in
                                                                    (match uu____9399
                                                                    with
                                                                    | 
                                                                    (bs1,comp1)
                                                                    ->
                                                                    let uu____9614
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    bs1  in
                                                                    (match uu____9614
                                                                    with
                                                                    | 
                                                                    (d_ps,bs2)
                                                                    ->
                                                                    let uu____9687
                                                                    =
                                                                    let uu____9689
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1  in
                                                                    Prims.op_Negation
                                                                    uu____9689
                                                                     in
                                                                    failwhen
                                                                    uu____9687
                                                                    "not total?"
                                                                    (fun
                                                                    uu____9708
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
                                                                    uu___6_9725
                                                                    =
                                                                    match uu___6_9725
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____9729)
                                                                    -> true
                                                                    | 
                                                                    uu____9732
                                                                    -> false
                                                                     in
                                                                    let uu____9736
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____9736
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
                                                                    uu____9872
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
                                                                    uu____9934
                                                                     ->
                                                                    match uu____9934
                                                                    with
                                                                    | 
                                                                    ((bv,uu____9954),
                                                                    (t,uu____9956))
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
                                                                    uu____10026
                                                                     ->
                                                                    match uu____10026
                                                                    with
                                                                    | 
                                                                    ((bv,uu____10053),
                                                                    (t,uu____10055))
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
                                                                    uu____10114
                                                                     ->
                                                                    match uu____10114
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
                                                                    let uu____10169
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1359_10193
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1359_10193.FStar_TypeChecker_Env.erasable_types_tab)
                                                                    }) s_ty1
                                                                    pat  in
                                                                    match uu____10169
                                                                    with
                                                                    | 
                                                                    (uu____10207,uu____10208,uu____10209,uu____10210,pat_t,uu____10212,_guard_pat,_erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____10226
                                                                    =
                                                                    let uu____10227
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____10227
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____10226
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____10232
                                                                    =
                                                                    let uu____10241
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____10241]
                                                                     in
                                                                    let uu____10260
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____10232
                                                                    uu____10260
                                                                     in
                                                                    let nty =
                                                                    let uu____10266
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu____10266
                                                                     in
                                                                    let uu____10269
                                                                    =
                                                                    FStar_Tactics_Monad.new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10269
                                                                    (fun
                                                                    uu____10299
                                                                     ->
                                                                    match uu____10299
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
                                                                    let uu____10326
                                                                    =
                                                                    let uu____10337
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____10337]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____10326
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____10373
                                                                    =
                                                                    let uu____10384
                                                                    =
                                                                    let uu____10389
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs3)  in
                                                                    (fv1,
                                                                    uu____10389)
                                                                     in
                                                                    (g', br,
                                                                    uu____10384)
                                                                     in
                                                                    FStar_Tactics_Monad.ret
                                                                    uu____10373)))))))
                                                                    | 
                                                                    uu____10410
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids
                                                                 in
                                                              FStar_Tactics_Monad.bind
                                                                uu____9244
                                                                (fun goal_brs
                                                                    ->
                                                                   let uu____10460
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs
                                                                     in
                                                                   match uu____10460
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
                                                                    let uu____10533
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10533
                                                                    (fun
                                                                    uu____10544
                                                                     ->
                                                                    let uu____10545
                                                                    =
                                                                    FStar_Tactics_Monad.add_goals
                                                                    goals  in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10545
                                                                    (fun
                                                                    uu____10555
                                                                     ->
                                                                    FStar_Tactics_Monad.ret
                                                                    infos)))))
                                            | uu____10562 ->
                                                FStar_Tactics_Monad.fail
                                                  "not an inductive type"))))))
       in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "destruct") uu____8959
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____10611::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____10641 = init xs  in x :: uu____10641
  
let rec (inspect :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Tactics_Monad.tac)
  =
  fun t  ->
    let uu____10654 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____10663) -> inspect t4
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
          let uu____10729 = last args  in
          (match uu____10729 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____10759 =
                 let uu____10760 =
                   let uu____10765 =
                     let uu____10766 =
                       let uu____10771 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____10771  in
                     uu____10766 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____10765, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____10760  in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10759)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____10782,uu____10783) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____10836 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____10836 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____10878 =
                      let uu____10879 =
                        let uu____10884 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____10884)  in
                      FStar_Reflection_Data.Tv_Abs uu____10879  in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10878))
      | FStar_Syntax_Syntax.Tm_type uu____10887 ->
          FStar_All.pipe_left FStar_Tactics_Monad.ret
            (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10912 ->
          let uu____10927 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____10927 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10958 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____10958 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____11011 -> failwith "impossible"  in
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____11024 =
            let uu____11025 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____11025  in
          FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11024
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____11046 =
            let uu____11047 =
              let uu____11052 =
                let uu____11053 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____11053  in
              (uu____11052, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____11047  in
          FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11046
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then
            FStar_All.pipe_left FStar_Tactics_Monad.ret
              FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____11093 ->
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____11098 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____11098 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____11151 ->
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
             | FStar_Util.Inr uu____11195 ->
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____11199 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____11199 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____11219 ->
                                FStar_Tactics_Monad.ret
                                  FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left FStar_Tactics_Monad.ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true,
                                       (lb1.FStar_Syntax_Syntax.lbattrs),
                                       bv1, (lb1.FStar_Syntax_Syntax.lbdef),
                                       t22)))
                       | uu____11227 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____11282 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____11282
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____11303 =
                  let uu____11315 =
                    FStar_List.map
                      (fun uu____11339  ->
                         match uu____11339 with
                         | (p1,b) ->
                             let uu____11360 = inspect_pat p1  in
                             (uu____11360, b)) ps
                     in
                  (fv, uu____11315)  in
                FStar_Reflection_Data.Pat_Cons uu____11303
            | FStar_Syntax_Syntax.Pat_var bv ->
                FStar_Reflection_Data.Pat_Var bv
            | FStar_Syntax_Syntax.Pat_wild bv ->
                FStar_Reflection_Data.Pat_Wild bv
            | FStar_Syntax_Syntax.Pat_dot_term (bv,t5) ->
                FStar_Reflection_Data.Pat_Dot_Term (bv, t5)
             in
          let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
          let brs2 =
            FStar_List.map
              (fun uu___7_11456  ->
                 match uu___7_11456 with
                 | (pat,uu____11478,t5) ->
                     let uu____11496 = inspect_pat pat  in (uu____11496, t5))
              brs1
             in
          FStar_All.pipe_left FStar_Tactics_Monad.ret
            (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left FStar_Tactics_Monad.ret
            FStar_Reflection_Data.Tv_Unknown
      | uu____11505 ->
          ((let uu____11507 =
              let uu____11513 =
                let uu____11515 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____11517 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____11515 uu____11517
                 in
              (FStar_Errors.Warning_CantInspect, uu____11513)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____11507);
           FStar_All.pipe_left FStar_Tactics_Monad.ret
             FStar_Reflection_Data.Tv_Unknown)
       in
    FStar_Tactics_Monad.wrap_err "inspect" uu____10654
  
let (pack :
  FStar_Reflection_Data.term_view ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____11535 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11535
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____11539 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11539
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____11543 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11543
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____11550 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11550
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____11575 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11575
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____11592 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11592
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left FStar_Tactics_Monad.ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____11611 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11611
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____11615 =
          let uu____11616 =
            let uu____11623 =
              let uu____11624 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____11624  in
            FStar_Syntax_Syntax.mk uu____11623  in
          uu____11616 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11615
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____11629 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11629
    | FStar_Reflection_Data.Tv_Let (false ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____11643 =
          let uu____11644 =
            let uu____11651 =
              let uu____11652 =
                let uu____11666 =
                  let uu____11669 =
                    let uu____11670 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____11670]  in
                  FStar_Syntax_Subst.close uu____11669 t2  in
                ((false, [lb]), uu____11666)  in
              FStar_Syntax_Syntax.Tm_let uu____11652  in
            FStar_Syntax_Syntax.mk uu____11651  in
          uu____11644 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11643
    | FStar_Reflection_Data.Tv_Let (true ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____11715 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____11715 with
         | (lbs,body) ->
             let uu____11730 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11730)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____11767 =
                let uu____11768 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____11768  in
              FStar_All.pipe_left wrap uu____11767
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____11785 =
                let uu____11786 =
                  let uu____11800 =
                    FStar_List.map
                      (fun uu____11824  ->
                         match uu____11824 with
                         | (p1,b) ->
                             let uu____11839 = pack_pat p1  in
                             (uu____11839, b)) ps
                     in
                  (fv, uu____11800)  in
                FStar_Syntax_Syntax.Pat_cons uu____11786  in
              FStar_All.pipe_left wrap uu____11785
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
            (fun uu___8_11887  ->
               match uu___8_11887 with
               | (pat,t1) ->
                   let uu____11904 = pack_pat pat  in
                   (uu____11904, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____11952 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11952
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____11980 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11980
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____12026 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____12026
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____12065 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____12065
  
let (lget :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty  ->
    fun k  ->
      let uu____12085 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps  ->
             let uu____12091 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____12091 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Tactics_Monad.fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lget") uu____12085
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____12125 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps  ->
               let ps1 =
                 let uu___1663_12132 = ps  in
                 let uu____12133 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___1663_12132.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___1663_12132.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___1663_12132.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___1663_12132.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___1663_12132.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___1663_12132.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___1663_12132.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___1663_12132.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___1663_12132.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___1663_12132.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___1663_12132.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____12133
                 }  in
               FStar_Tactics_Monad.set ps1)
           in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lset") uu____12125
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____12160 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____12160 with
      | (u,ctx_uvars,g_u) ->
          let uu____12193 = FStar_List.hd ctx_uvars  in
          (match uu____12193 with
           | (ctx_uvar,uu____12207) ->
               let g =
                 let uu____12209 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____12209 false
                   ""
                  in
               (g, g_u))
  
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu____12218 = FStar_TypeChecker_Env.clear_expected_typ env  in
    match uu____12218 with
    | (env1,uu____12226) ->
        let env2 =
          let uu___1680_12232 = env1  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1680_12232.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1680_12232.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1680_12232.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1680_12232.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1680_12232.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1680_12232.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1680_12232.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1680_12232.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1680_12232.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1680_12232.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___1680_12232.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1680_12232.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1680_12232.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1680_12232.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1680_12232.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1680_12232.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1680_12232.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1680_12232.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1680_12232.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1680_12232.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1680_12232.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1680_12232.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1680_12232.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1680_12232.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1680_12232.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1680_12232.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1680_12232.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1680_12232.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1680_12232.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1680_12232.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1680_12232.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1680_12232.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1680_12232.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1680_12232.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1680_12232.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1680_12232.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1680_12232.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1680_12232.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1680_12232.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1680_12232.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1680_12232.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1680_12232.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1680_12232.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1680_12232.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1680_12232.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1680_12232.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let env3 =
          let uu___1683_12235 = env2  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1683_12235.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1683_12235.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1683_12235.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1683_12235.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1683_12235.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1683_12235.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1683_12235.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1683_12235.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1683_12235.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1683_12235.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1683_12235.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1683_12235.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1683_12235.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1683_12235.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1683_12235.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1683_12235.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1683_12235.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1683_12235.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1683_12235.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1683_12235.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1683_12235.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1683_12235.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1683_12235.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___1683_12235.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1683_12235.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1683_12235.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1683_12235.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1683_12235.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1683_12235.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1683_12235.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1683_12235.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1683_12235.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1683_12235.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1683_12235.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1683_12235.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1683_12235.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1683_12235.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1683_12235.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1683_12235.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1683_12235.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1683_12235.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1683_12235.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1683_12235.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1683_12235.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1683_12235.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1683_12235.FStar_TypeChecker_Env.erasable_types_tab)
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
            let uu____12268 =
              FStar_TypeChecker_Env.debug env1
                (FStar_Options.Other "TacVerbose")
               in
            let uu____12271 = FStar_Util.psmap_empty ()  in
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
              FStar_Tactics_Types.tac_verb_dbg = uu____12268;
              FStar_Tactics_Types.local_state = uu____12271
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
        let uu____12297 = goal_of_goal_ty env1 typ  in
        match uu____12297 with
        | (g,g_u) ->
            let ps =
              proofstate_of_goals rng env1 [g]
                g_u.FStar_TypeChecker_Common.implicits
               in
            let uu____12309 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____12309)
  
let (goal_of_implicit :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicit -> FStar_Tactics_Types.goal)
  =
  fun env  ->
    fun i  ->
      let uu____12321 = FStar_Options.peek ()  in
      FStar_Tactics_Types.mk_goal env i.FStar_TypeChecker_Common.imp_uvar
        uu____12321 false ""
  
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
          let uu____12348 = FStar_List.hd goals  in
          FStar_Tactics_Types.goal_witness uu____12348  in
        let ps =
          let uu____12350 =
            FStar_TypeChecker_Env.debug env
              (FStar_Options.Other "TacVerbose")
             in
          let uu____12353 = FStar_Util.psmap_empty ()  in
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
            FStar_Tactics_Types.tac_verb_dbg = uu____12350;
            FStar_Tactics_Types.local_state = uu____12353
          }  in
        (ps, w)
  