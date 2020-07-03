open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun e ->
      fun t ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
let (bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> normalize [] e t
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> FStar_TypeChecker_Normalize.unfold_whnf e t
let (tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  FStar_TypeChecker_Normalize.term_to_string
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun e ->
    fun t ->
      FStar_Syntax_Print.term_to_string' e.FStar_TypeChecker_Env.dsenv t
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g ->
    let uu____65 =
      let uu____66 = FStar_Tactics_Types.goal_env g in
      let uu____67 = FStar_Tactics_Types.goal_type g in
      bnorm uu____66 uu____67 in
    FStar_Tactics_Types.goal_with_type g uu____65
let (tacprint : Prims.string -> unit) =
  fun s -> FStar_Util.print1 "TAC>> %s\n" s
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      let uu____92 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____92
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        let uu____117 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____117
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        fun z ->
          let uu____149 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____149
let (print : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    (let uu____165 =
       let uu____167 = FStar_Options.silent () in Prims.op_Negation uu____167 in
     if uu____165 then tacprint msg else ());
    FStar_Tactics_Monad.ret ()
let (debugging : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____180 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let uu____188 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac") in
         FStar_Tactics_Monad.ret uu____188)
let (dump : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst = FStar_TypeChecker_Cfg.psc_subst psc in
         (let uu____212 = FStar_Tactics_Types.subst_proof_state subst ps in
          FStar_Tactics_Printing.do_dump_proofstate uu____212 msg);
         FStar_Tactics_Result.Success ((), ps))
let fail1 :
  'uuuuuu220 .
    Prims.string -> Prims.string -> 'uuuuuu220 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      let uu____237 = FStar_Util.format1 msg x in
      FStar_Tactics_Monad.fail uu____237
let fail2 :
  'uuuuuu248 .
    Prims.string ->
      Prims.string -> Prims.string -> 'uuuuuu248 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        let uu____272 = FStar_Util.format2 msg x y in
        FStar_Tactics_Monad.fail uu____272
let fail3 :
  'uuuuuu285 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> 'uuuuuu285 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          let uu____316 = FStar_Util.format3 msg x y z in
          FStar_Tactics_Monad.fail uu____316
let fail4 :
  'uuuuuu331 .
    Prims.string ->
      Prims.string ->
        Prims.string ->
          Prims.string -> Prims.string -> 'uuuuuu331 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          fun w ->
            let uu____369 = FStar_Util.format4 msg x y z w in
            FStar_Tactics_Monad.fail uu____369
let catch :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (Prims.exn, 'a) FStar_Util.either FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____404 = FStar_Tactics_Monad.run t ps in
         match uu____404 with
         | FStar_Tactics_Result.Success (a1, q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a1), q))
         | FStar_Tactics_Result.Failed (m, q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___68_428 = ps in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___68_428.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___68_428.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___68_428.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___68_428.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___68_428.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___68_428.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___68_428.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___68_428.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___68_428.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___68_428.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___68_428.FStar_Tactics_Types.local_state)
                 } in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
let recover :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (Prims.exn, 'a) FStar_Util.either FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let uu____467 = FStar_Tactics_Monad.run t ps in
         match uu____467 with
         | FStar_Tactics_Result.Success (a1, q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a1), q)
         | FStar_Tactics_Result.Failed (m, q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
let trytac :
  'a .
    'a FStar_Tactics_Monad.tac ->
      'a FStar_Pervasives_Native.option FStar_Tactics_Monad.tac
  =
  fun t ->
    let uu____515 = catch t in
    FStar_Tactics_Monad.bind uu____515
      (fun r ->
         match r with
         | FStar_Util.Inr v ->
             FStar_Tactics_Monad.ret (FStar_Pervasives_Native.Some v)
         | FStar_Util.Inl uu____542 ->
             FStar_Tactics_Monad.ret FStar_Pervasives_Native.None)
let trytac_exn :
  'a .
    'a FStar_Tactics_Monad.tac ->
      'a FStar_Pervasives_Native.option FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         try
           (fun uu___94_574 ->
              match () with
              | () ->
                  let uu____579 = trytac t in
                  FStar_Tactics_Monad.run uu____579 ps) ()
         with
         | FStar_Errors.Err (uu____595, msg) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____601 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____607, msg, uu____609) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____614 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        (let uu____643 =
           FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "1346") in
         if uu____643
         then
           let uu____647 = FStar_Syntax_Print.term_to_string t1 in
           let uu____649 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____647
             uu____649
         else ());
        (try
           (fun uu___114_660 ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env1 t1 t2 in
                  ((let uu____668 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "1346") in
                    if uu____668
                    then
                      let uu____672 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env1) res in
                      let uu____674 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____676 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____672
                        uu____674 uu____676
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____687 =
                          FStar_Tactics_Monad.add_implicits
                            g.FStar_TypeChecker_Common.implicits in
                        FStar_Tactics_Monad.bind uu____687
                          (fun uu____692 -> FStar_Tactics_Monad.ret true))))
             ()
         with
         | FStar_Errors.Err (uu____702, msg) ->
             FStar_Tactics_Monad.mlog
               (fun uu____708 ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____711 -> FStar_Tactics_Monad.ret false)
         | FStar_Errors.Error (uu____714, msg, r) ->
             FStar_Tactics_Monad.mlog
               (fun uu____722 ->
                  let uu____723 = FStar_Range.string_of_range r in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____723)
               (fun uu____727 -> FStar_Tactics_Monad.ret false))
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____756 ->
             (let uu____758 =
                FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "1346") in
              if uu____758
              then
                (FStar_Options.push ();
                 (let uu____763 =
                    FStar_Options.set_options
                      "--debug_level Rel --debug_level RelCheck" in
                  ()))
              else ());
             (let uu____767 = __do_unify env1 t1 t2 in
              FStar_Tactics_Monad.bind uu____767
                (fun r ->
                   (let uu____778 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "1346") in
                    if uu____778 then FStar_Options.pop () else ());
                   FStar_Tactics_Monad.ret r)))
let (do_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uvs1 = FStar_Syntax_Free.uvars_uncached t1 in
        let uu____810 = do_unify env1 t1 t2 in
        FStar_Tactics_Monad.bind uu____810
          (fun r ->
             if r
             then
               let uvs2 = FStar_Syntax_Free.uvars_uncached t1 in
               let uu____828 =
                 let uu____830 = FStar_Util.set_eq uvs1 uvs2 in
                 Prims.op_Negation uu____830 in
               (if uu____828
                then FStar_Tactics_Monad.ret false
                else FStar_Tactics_Monad.ret true)
             else FStar_Tactics_Monad.ret false)
let (set_solution :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____861 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
      match uu____861 with
      | FStar_Pervasives_Native.Some uu____866 ->
          let uu____867 =
            let uu____869 =
              FStar_Tactics_Printing.goal_to_string_verbose goal in
            FStar_Util.format1 "Goal %s is already solved" uu____869 in
          FStar_Tactics_Monad.fail uu____867
      | FStar_Pervasives_Native.None ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           FStar_Tactics_Monad.ret ())
let (trysolve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____890 = FStar_Tactics_Types.goal_env goal in
      let uu____891 = FStar_Tactics_Types.goal_witness goal in
      do_unify uu____890 solution uu____891
let (solve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let e = FStar_Tactics_Types.goal_env goal in
      FStar_Tactics_Monad.mlog
        (fun uu____911 ->
           let uu____912 =
             let uu____914 = FStar_Tactics_Types.goal_witness goal in
             FStar_Syntax_Print.term_to_string uu____914 in
           let uu____915 = FStar_Syntax_Print.term_to_string solution in
           FStar_Util.print2 "solve %s := %s\n" uu____912 uu____915)
        (fun uu____920 ->
           let uu____921 = trysolve goal solution in
           FStar_Tactics_Monad.bind uu____921
             (fun b ->
                if b
                then
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____933 -> FStar_Tactics_Monad.remove_solved_goals)
                else
                  (let uu____936 =
                     let uu____938 =
                       let uu____940 = FStar_Tactics_Types.goal_env goal in
                       tts uu____940 solution in
                     let uu____941 =
                       let uu____943 = FStar_Tactics_Types.goal_env goal in
                       let uu____944 = FStar_Tactics_Types.goal_witness goal in
                       tts uu____943 uu____944 in
                     let uu____945 =
                       let uu____947 = FStar_Tactics_Types.goal_env goal in
                       let uu____948 = FStar_Tactics_Types.goal_type goal in
                       tts uu____947 uu____948 in
                     FStar_Util.format3 "%s does not solve %s : %s" uu____938
                       uu____941 uu____945 in
                   FStar_Tactics_Monad.fail uu____936)))
let (solve' :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____965 = set_solution goal solution in
      FStar_Tactics_Monad.bind uu____965
        (fun uu____969 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
             (fun uu____971 -> FStar_Tactics_Monad.remove_solved_goals))
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____980 = FStar_Syntax_Util.un_squash t1 in
    match uu____980 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t' in
        let uu____992 =
          let uu____993 = FStar_Syntax_Subst.compress t'1 in
          uu____993.FStar_Syntax_Syntax.n in
        (match uu____992 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____998 -> false)
    | uu____1000 -> false
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1013 = FStar_Syntax_Util.un_squash t in
    match uu____1013 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1024 =
          let uu____1025 = FStar_Syntax_Subst.compress t' in
          uu____1025.FStar_Syntax_Syntax.n in
        (match uu____1024 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1030 -> false)
    | uu____1032 -> false
let (tadmit_t : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____1048 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                (let uu____1057 =
                   let uu____1058 = FStar_Tactics_Types.goal_type g in
                   uu____1058.FStar_Syntax_Syntax.pos in
                 let uu____1061 =
                   let uu____1067 =
                     let uu____1069 =
                       FStar_Tactics_Printing.goal_to_string ""
                         FStar_Pervasives_Native.None ps g in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1069 in
                   (FStar_Errors.Warning_TacAdmit, uu____1067) in
                 FStar_Errors.log_issue uu____1057 uu____1061);
                solve' g t)) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tadmit_t") uu____1048
let (fresh : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1092 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let n = ps.FStar_Tactics_Types.freshness in
         let ps1 =
           let uu___200_1103 = ps in
           {
             FStar_Tactics_Types.main_context =
               (uu___200_1103.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (uu___200_1103.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___200_1103.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___200_1103.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___200_1103.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___200_1103.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___200_1103.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___200_1103.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___200_1103.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___200_1103.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___200_1103.FStar_Tactics_Types.local_state)
           } in
         let uu____1105 = FStar_Tactics_Monad.set ps1 in
         FStar_Tactics_Monad.bind uu____1105
           (fun uu____1110 ->
              let uu____1111 = FStar_BigInt.of_int_fs n in
              FStar_Tactics_Monad.ret uu____1111))
let (curms : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1119 ->
    let uu____1122 =
      let uu____1123 = FStar_Util.now_ms () in
      FStar_All.pipe_right uu____1123 FStar_BigInt.of_int_fs in
    FStar_Tactics_Monad.ret uu____1122
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1169 ->
                let uu____1170 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1170)
             (fun uu____1175 ->
                let e1 =
                  let uu___209_1177 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___209_1177.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___209_1177.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___209_1177.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___209_1177.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___209_1177.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___209_1177.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___209_1177.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___209_1177.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___209_1177.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___209_1177.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___209_1177.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___209_1177.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___209_1177.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___209_1177.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___209_1177.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___209_1177.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___209_1177.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___209_1177.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___209_1177.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___209_1177.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___209_1177.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___209_1177.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___209_1177.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___209_1177.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___209_1177.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___209_1177.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___209_1177.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___209_1177.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___209_1177.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___209_1177.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___209_1177.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___209_1177.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___209_1177.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___209_1177.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___209_1177.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___209_1177.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___209_1177.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___209_1177.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___209_1177.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___209_1177.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___209_1177.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___209_1177.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___209_1177.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___209_1177.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___209_1177.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___209_1177.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___213_1189 ->
                     match () with
                     | () ->
                         let uu____1198 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t in
                         FStar_Tactics_Monad.ret uu____1198) ()
                with
                | FStar_Errors.Err (uu____1225, msg) ->
                    let uu____1229 = tts e1 t in
                    let uu____1231 =
                      let uu____1233 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1233
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1229 uu____1231 msg
                | FStar_Errors.Error (uu____1243, msg, uu____1245) ->
                    let uu____1248 = tts e1 t in
                    let uu____1250 =
                      let uu____1252 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1252
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1248 uu____1250 msg))
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1305 ->
                let uu____1306 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____1306)
             (fun uu____1311 ->
                let e1 =
                  let uu___230_1313 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___230_1313.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___230_1313.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___230_1313.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___230_1313.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___230_1313.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___230_1313.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___230_1313.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___230_1313.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___230_1313.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___230_1313.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___230_1313.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___230_1313.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___230_1313.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___230_1313.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___230_1313.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___230_1313.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___230_1313.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___230_1313.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___230_1313.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___230_1313.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___230_1313.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___230_1313.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___230_1313.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___230_1313.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___230_1313.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___230_1313.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___230_1313.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___230_1313.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___230_1313.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___230_1313.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___230_1313.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___230_1313.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___230_1313.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___230_1313.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___230_1313.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___230_1313.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___230_1313.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___230_1313.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___230_1313.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___230_1313.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___230_1313.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___230_1313.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___230_1313.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___230_1313.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___230_1313.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___230_1313.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___234_1328 ->
                     match () with
                     | () ->
                         let uu____1337 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t in
                         (match uu____1337 with
                          | (t1, lc, g) ->
                              FStar_Tactics_Monad.ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu____1375, msg) ->
                    let uu____1379 = tts e1 t in
                    let uu____1381 =
                      let uu____1383 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1383
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1379 uu____1381 msg
                | FStar_Errors.Error (uu____1393, msg, uu____1395) ->
                    let uu____1398 = tts e1 t in
                    let uu____1400 =
                      let uu____1402 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1402
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1398 uu____1400 msg))
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1455 ->
                let uu____1456 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_lax(%s)\n" uu____1456)
             (fun uu____1462 ->
                let e1 =
                  let uu___255_1464 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___255_1464.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___255_1464.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___255_1464.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___255_1464.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___255_1464.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___255_1464.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___255_1464.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___255_1464.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___255_1464.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___255_1464.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___255_1464.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___255_1464.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___255_1464.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___255_1464.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___255_1464.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___255_1464.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___255_1464.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___255_1464.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___255_1464.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___255_1464.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___255_1464.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___255_1464.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___255_1464.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___255_1464.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___255_1464.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___255_1464.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___255_1464.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___255_1464.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___255_1464.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___255_1464.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___255_1464.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___255_1464.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___255_1464.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___255_1464.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___255_1464.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___255_1464.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___255_1464.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___255_1464.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___255_1464.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___255_1464.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___255_1464.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___255_1464.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___255_1464.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___255_1464.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___255_1464.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___255_1464.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                let e2 =
                  let uu___258_1467 = e1 in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___258_1467.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___258_1467.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___258_1467.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___258_1467.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___258_1467.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___258_1467.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___258_1467.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___258_1467.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___258_1467.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___258_1467.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___258_1467.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___258_1467.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___258_1467.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___258_1467.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___258_1467.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___258_1467.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___258_1467.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___258_1467.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___258_1467.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___258_1467.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___258_1467.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___258_1467.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___258_1467.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___258_1467.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___258_1467.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___258_1467.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___258_1467.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___258_1467.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___258_1467.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___258_1467.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___258_1467.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___258_1467.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___258_1467.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___258_1467.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___258_1467.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___258_1467.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___258_1467.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___258_1467.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___258_1467.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___258_1467.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___258_1467.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___258_1467.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___258_1467.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___258_1467.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___258_1467.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___258_1467.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___262_1479 ->
                     match () with
                     | () ->
                         let uu____1488 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t in
                         FStar_Tactics_Monad.ret uu____1488) ()
                with
                | FStar_Errors.Err (uu____1515, msg) ->
                    let uu____1519 = tts e2 t in
                    let uu____1521 =
                      let uu____1523 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1523
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1519 uu____1521 msg
                | FStar_Errors.Error (uu____1533, msg, uu____1535) ->
                    let uu____1538 = tts e2 t in
                    let uu____1540 =
                      let uu____1542 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1542
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1538 uu____1540 msg))
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t ->
      let steps =
        [FStar_TypeChecker_Env.Reify;
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.UnfoldTac;
        FStar_TypeChecker_Env.Unmeta] in
      let t1 = normalize steps e t in is_true t1
let (get_guard_policy :
  unit -> FStar_Tactics_Types.guard_policy FStar_Tactics_Monad.tac) =
  fun uu____1576 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps -> FStar_Tactics_Monad.ret ps.FStar_Tactics_Types.guard_policy)
let (set_guard_policy :
  FStar_Tactics_Types.guard_policy -> unit FStar_Tactics_Monad.tac) =
  fun pol ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_Tactics_Monad.set
           (let uu___283_1595 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___283_1595.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___283_1595.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___283_1595.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___283_1595.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___283_1595.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___283_1595.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___283_1595.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___283_1595.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___283_1595.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___283_1595.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___283_1595.FStar_Tactics_Types.local_state)
            }))
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun pol ->
    fun t ->
      let uu____1620 = get_guard_policy () in
      FStar_Tactics_Monad.bind uu____1620
        (fun old_pol ->
           let uu____1626 = set_guard_policy pol in
           FStar_Tactics_Monad.bind uu____1626
             (fun uu____1630 ->
                FStar_Tactics_Monad.bind t
                  (fun r ->
                     let uu____1634 = set_guard_policy old_pol in
                     FStar_Tactics_Monad.bind uu____1634
                       (fun uu____1638 -> FStar_Tactics_Monad.ret r))))
let (getopts : FStar_Options.optionstate FStar_Tactics_Monad.tac) =
  let uu____1642 = trytac FStar_Tactics_Monad.cur_goal in
  FStar_Tactics_Monad.bind uu____1642
    (fun uu___0_1651 ->
       match uu___0_1651 with
       | FStar_Pervasives_Native.Some g ->
           FStar_Tactics_Monad.ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None ->
           let uu____1657 = FStar_Options.peek () in
           FStar_Tactics_Monad.ret uu____1657)
let (proc_guard :
  Prims.string ->
    env -> FStar_TypeChecker_Common.guard_t -> unit FStar_Tactics_Monad.tac)
  =
  fun reason ->
    fun e ->
      fun g ->
        FStar_Tactics_Monad.mlog
          (fun uu____1682 ->
             let uu____1683 = FStar_TypeChecker_Rel.guard_to_string e g in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____1683)
          (fun uu____1688 ->
             let uu____1689 =
               FStar_Tactics_Monad.add_implicits
                 g.FStar_TypeChecker_Common.implicits in
             FStar_Tactics_Monad.bind uu____1689
               (fun uu____1693 ->
                  FStar_Tactics_Monad.bind getopts
                    (fun opts ->
                       let uu____1697 =
                         let uu____1698 =
                           FStar_TypeChecker_Rel.simplify_guard e g in
                         uu____1698.FStar_TypeChecker_Common.guard_f in
                       match uu____1697 with
                       | FStar_TypeChecker_Common.Trivial ->
                           FStar_Tactics_Monad.ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____1702 = istrivial e f in
                           if uu____1702
                           then FStar_Tactics_Monad.ret ()
                           else
                             FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
                               (fun ps ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop ->
                                      ((let uu____1715 =
                                          let uu____1721 =
                                            let uu____1723 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____1723 in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____1721) in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____1715);
                                       FStar_Tactics_Monad.ret ())
                                  | FStar_Tactics_Types.Goal ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1729 ->
                                           let uu____1730 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____1730)
                                        (fun uu____1735 ->
                                           let uu____1736 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts "" in
                                           FStar_Tactics_Monad.bind
                                             uu____1736
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___312_1744 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___312_1744.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___312_1744.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___312_1744.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___312_1744.FStar_Tactics_Types.label)
                                                  } in
                                                FStar_Tactics_Monad.push_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.SMT ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1748 ->
                                           let uu____1749 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____1749)
                                        (fun uu____1754 ->
                                           let uu____1755 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts "" in
                                           FStar_Tactics_Monad.bind
                                             uu____1755
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___319_1763 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___319_1763.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___319_1763.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___319_1763.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___319_1763.FStar_Tactics_Types.label)
                                                  } in
                                                FStar_Tactics_Monad.push_smt_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.Force ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1767 ->
                                           let uu____1768 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____1768)
                                        (fun uu____1772 ->
                                           try
                                             (fun uu___326_1777 ->
                                                match () with
                                                | () ->
                                                    let uu____1780 =
                                                      let uu____1782 =
                                                        let uu____1784 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____1784 in
                                                      Prims.op_Negation
                                                        uu____1782 in
                                                    if uu____1780
                                                    then
                                                      FStar_Tactics_Monad.mlog
                                                        (fun uu____1791 ->
                                                           let uu____1792 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____1792)
                                                        (fun uu____1796 ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else
                                                      FStar_Tactics_Monad.ret
                                                        ()) ()
                                           with
                                           | uu___325_1801 ->
                                               FStar_Tactics_Monad.mlog
                                                 (fun uu____1806 ->
                                                    let uu____1807 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____1807)
                                                 (fun uu____1811 ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
let (tcc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu____1828 =
        let uu____1831 = __tc_lax e t in
        FStar_Tactics_Monad.bind uu____1831
          (fun uu____1851 ->
             match uu____1851 with
             | (uu____1860, lc, uu____1862) ->
                 let uu____1863 =
                   let uu____1864 = FStar_TypeChecker_Common.lcomp_comp lc in
                   FStar_All.pipe_right uu____1864
                     FStar_Pervasives_Native.fst in
                 FStar_Tactics_Monad.ret uu____1863) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tcc") uu____1828
let (tc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Reflection_Data.typ FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu____1893 =
        let uu____1898 = tcc e t in
        FStar_Tactics_Monad.bind uu____1898
          (fun c -> FStar_Tactics_Monad.ret (FStar_Syntax_Util.comp_result c)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tc") uu____1893
let (trivial : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____1923 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____1929 =
           let uu____1931 = FStar_Tactics_Types.goal_env goal in
           let uu____1932 = FStar_Tactics_Types.goal_type goal in
           istrivial uu____1931 uu____1932 in
         if uu____1929
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____1938 =
              let uu____1940 = FStar_Tactics_Types.goal_env goal in
              let uu____1941 = FStar_Tactics_Types.goal_type goal in
              tts uu____1940 uu____1941 in
            fail1 "Not a trivial goal: %s" uu____1938))
let divide :
  'a 'b .
    FStar_BigInt.t ->
      'a FStar_Tactics_Monad.tac ->
        'b FStar_Tactics_Monad.tac -> ('a * 'b) FStar_Tactics_Monad.tac
  =
  fun n ->
    fun l ->
      fun r ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun p ->
             let uu____1992 =
               try
                 (fun uu___377_2015 ->
                    match () with
                    | () ->
                        let uu____2026 =
                          let uu____2035 = FStar_BigInt.to_int_fs n in
                          FStar_List.splitAt uu____2035
                            p.FStar_Tactics_Types.goals in
                        FStar_Tactics_Monad.ret uu____2026) ()
               with
               | uu___376_2046 ->
                   FStar_Tactics_Monad.fail "divide: not enough goals" in
             FStar_Tactics_Monad.bind uu____1992
               (fun uu____2083 ->
                  match uu____2083 with
                  | (lgs, rgs) ->
                      let lp =
                        let uu___359_2109 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___359_2109.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___359_2109.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___359_2109.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___359_2109.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___359_2109.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___359_2109.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___359_2109.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___359_2109.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___359_2109.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___359_2109.FStar_Tactics_Types.local_state)
                        } in
                      let uu____2110 = FStar_Tactics_Monad.set lp in
                      FStar_Tactics_Monad.bind uu____2110
                        (fun uu____2118 ->
                           FStar_Tactics_Monad.bind l
                             (fun a1 ->
                                FStar_Tactics_Monad.bind
                                  FStar_Tactics_Monad.get
                                  (fun lp' ->
                                     let rp =
                                       let uu___365_2134 = lp' in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___365_2134.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___365_2134.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___365_2134.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___365_2134.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___365_2134.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___365_2134.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___365_2134.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___365_2134.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___365_2134.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___365_2134.FStar_Tactics_Types.local_state)
                                       } in
                                     let uu____2135 =
                                       FStar_Tactics_Monad.set rp in
                                     FStar_Tactics_Monad.bind uu____2135
                                       (fun uu____2143 ->
                                          FStar_Tactics_Monad.bind r
                                            (fun b1 ->
                                               FStar_Tactics_Monad.bind
                                                 FStar_Tactics_Monad.get
                                                 (fun rp' ->
                                                    let p' =
                                                      let uu___371_2159 = rp' in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___371_2159.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___371_2159.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___371_2159.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___371_2159.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___371_2159.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___371_2159.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___371_2159.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___371_2159.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___371_2159.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___371_2159.FStar_Tactics_Types.local_state)
                                                      } in
                                                    let uu____2160 =
                                                      FStar_Tactics_Monad.set
                                                        p' in
                                                    FStar_Tactics_Monad.bind
                                                      uu____2160
                                                      (fun uu____2168 ->
                                                         FStar_Tactics_Monad.bind
                                                           FStar_Tactics_Monad.remove_solved_goals
                                                           (fun uu____2174 ->
                                                              FStar_Tactics_Monad.ret
                                                                (a1, b1)))))))))))
let focus : 'a . 'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac =
  fun f ->
    let uu____2196 = divide FStar_BigInt.one f FStar_Tactics_Monad.idtac in
    FStar_Tactics_Monad.bind uu____2196
      (fun uu____2209 ->
         match uu____2209 with | (a1, ()) -> FStar_Tactics_Monad.ret a1)
let rec map :
  'a . 'a FStar_Tactics_Monad.tac -> 'a Prims.list FStar_Tactics_Monad.tac =
  fun tau ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun p ->
         match p.FStar_Tactics_Types.goals with
         | [] -> FStar_Tactics_Monad.ret []
         | uu____2247::uu____2248 ->
             let uu____2251 =
               let uu____2260 = map tau in
               divide FStar_BigInt.one tau uu____2260 in
             FStar_Tactics_Monad.bind uu____2251
               (fun uu____2278 ->
                  match uu____2278 with
                  | (h, t) -> FStar_Tactics_Monad.ret (h :: t)))
let (seq :
  unit FStar_Tactics_Monad.tac ->
    unit FStar_Tactics_Monad.tac -> unit FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let uu____2320 =
        FStar_Tactics_Monad.bind t1
          (fun uu____2325 ->
             let uu____2326 = map t2 in
             FStar_Tactics_Monad.bind uu____2326
               (fun uu____2334 -> FStar_Tactics_Monad.ret ())) in
      focus uu____2320
let (intro : unit -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac) =
  fun uu____2344 ->
    let uu____2347 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____2356 =
             let uu____2363 =
               let uu____2364 = FStar_Tactics_Types.goal_env goal in
               let uu____2365 = FStar_Tactics_Types.goal_type goal in
               whnf uu____2364 uu____2365 in
             FStar_Syntax_Util.arrow_one uu____2363 in
           match uu____2356 with
           | FStar_Pervasives_Native.Some (b, c) ->
               let uu____2374 =
                 let uu____2376 = FStar_Syntax_Util.is_total_comp c in
                 Prims.op_Negation uu____2376 in
               if uu____2374
               then FStar_Tactics_Monad.fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2385 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.push_binders uu____2385 [b] in
                  let typ' = FStar_Syntax_Util.comp_result c in
                  let uu____2401 =
                    FStar_Tactics_Monad.new_uvar "intro" env' typ' in
                  FStar_Tactics_Monad.bind uu____2401
                    (fun uu____2418 ->
                       match uu____2418 with
                       | (body, ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)) in
                           let uu____2442 = set_solution goal sol in
                           FStar_Tactics_Monad.bind uu____2442
                             (fun uu____2448 ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label in
                                let uu____2450 =
                                  let uu____2453 = bnorm_goal g in
                                  FStar_Tactics_Monad.replace_cur uu____2453 in
                                FStar_Tactics_Monad.bind uu____2450
                                  (fun uu____2455 ->
                                     FStar_Tactics_Monad.ret b))))
           | FStar_Pervasives_Native.None ->
               let uu____2460 =
                 let uu____2462 = FStar_Tactics_Types.goal_env goal in
                 let uu____2463 = FStar_Tactics_Types.goal_type goal in
                 tts uu____2462 uu____2463 in
               fail1 "goal is not an arrow (%s)" uu____2460) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "intro") uu____2347
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder)
      FStar_Tactics_Monad.tac)
  =
  fun uu____2481 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2504 =
            let uu____2511 =
              let uu____2512 = FStar_Tactics_Types.goal_env goal in
              let uu____2513 = FStar_Tactics_Types.goal_type goal in
              whnf uu____2512 uu____2513 in
            FStar_Syntax_Util.arrow_one uu____2511 in
          match uu____2504 with
          | FStar_Pervasives_Native.Some (b, c) ->
              let uu____2526 =
                let uu____2528 = FStar_Syntax_Util.is_total_comp c in
                Prims.op_Negation uu____2528 in
              if uu____2526
              then FStar_Tactics_Monad.fail "Codomain is effectful"
              else
                (let bv =
                   let uu____2545 = FStar_Tactics_Types.goal_type goal in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____2545 in
                 let bs =
                   let uu____2556 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2556; b] in
                 let env' =
                   let uu____2582 = FStar_Tactics_Types.goal_env goal in
                   FStar_TypeChecker_Env.push_binders uu____2582 bs in
                 let uu____2583 =
                   FStar_Tactics_Monad.new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c) in
                 FStar_Tactics_Monad.bind uu____2583
                   (fun uu____2609 ->
                      match uu____2609 with
                      | (u, ctx_uvar_u) ->
                          let lb =
                            let uu____2623 =
                              FStar_Tactics_Types.goal_type goal in
                            let uu____2626 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____2623
                              FStar_Parser_Const.effect_Tot_lid uu____2626 []
                              FStar_Range.dummyRange in
                          let body = FStar_Syntax_Syntax.bv_to_name bv in
                          let uu____2644 =
                            FStar_Syntax_Subst.close_let_rec [lb] body in
                          (match uu____2644 with
                           | (lbs, body1) ->
                               let tm =
                                 let uu____2666 =
                                   let uu____2667 =
                                     FStar_Tactics_Types.goal_witness goal in
                                   uu____2667.FStar_Syntax_Syntax.pos in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1)) uu____2666 in
                               let uu____2683 = set_solution goal tm in
                               FStar_Tactics_Monad.bind uu____2683
                                 (fun uu____2692 ->
                                    let uu____2693 =
                                      let uu____2696 =
                                        bnorm_goal
                                          (let uu___442_2699 = goal in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___442_2699.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___442_2699.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___442_2699.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___442_2699.FStar_Tactics_Types.label)
                                           }) in
                                      FStar_Tactics_Monad.replace_cur
                                        uu____2696 in
                                    FStar_Tactics_Monad.bind uu____2693
                                      (fun uu____2706 ->
                                         let uu____2707 =
                                           let uu____2712 =
                                             FStar_Syntax_Syntax.mk_binder bv in
                                           (uu____2712, b) in
                                         FStar_Tactics_Monad.ret uu____2707)))))
          | FStar_Pervasives_Native.None ->
              let uu____2721 =
                let uu____2723 = FStar_Tactics_Types.goal_env goal in
                let uu____2724 = FStar_Tactics_Types.goal_type goal in
                tts uu____2723 uu____2724 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2721))
let (norm :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____2748 ->
              let uu____2749 =
                let uu____2751 = FStar_Tactics_Types.goal_witness goal in
                FStar_Syntax_Print.term_to_string uu____2751 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2749)
           (fun uu____2757 ->
              let steps =
                let uu____2761 = FStar_TypeChecker_Normalize.tr_norm_steps s in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____2761 in
              let t =
                let uu____2765 = FStar_Tactics_Types.goal_env goal in
                let uu____2766 = FStar_Tactics_Types.goal_type goal in
                normalize steps uu____2765 uu____2766 in
              let uu____2767 = FStar_Tactics_Types.goal_with_type goal t in
              FStar_Tactics_Monad.replace_cur uu____2767))
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun s ->
      fun t ->
        let uu____2792 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____2800 -> g.FStar_Tactics_Types.opts
                 | uu____2803 -> FStar_Options.peek () in
               FStar_Tactics_Monad.mlog
                 (fun uu____2808 ->
                    let uu____2809 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____2809)
                 (fun uu____2814 ->
                    let uu____2815 = __tc_lax e t in
                    FStar_Tactics_Monad.bind uu____2815
                      (fun uu____2836 ->
                         match uu____2836 with
                         | (t1, uu____2846, uu____2847) ->
                             let steps =
                               let uu____2851 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____2851 in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1 in
                             FStar_Tactics_Monad.mlog
                               (fun uu____2857 ->
                                  let uu____2858 =
                                    FStar_Syntax_Print.term_to_string t2 in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____2858)
                               (fun uu____2862 -> FStar_Tactics_Monad.ret t2)))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_term")
          uu____2792
let (refine_intro : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____2875 ->
    let uu____2878 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____2885 =
             let uu____2896 = FStar_Tactics_Types.goal_env g in
             let uu____2897 = FStar_Tactics_Types.goal_type g in
             FStar_TypeChecker_Rel.base_and_refinement uu____2896 uu____2897 in
           match uu____2885 with
           | (uu____2900, FStar_Pervasives_Native.None) ->
               FStar_Tactics_Monad.fail "not a refinement"
           | (t, FStar_Pervasives_Native.Some (bv, phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t in
               let uu____2926 =
                 let uu____2931 =
                   let uu____2936 =
                     let uu____2937 = FStar_Syntax_Syntax.mk_binder bv in
                     [uu____2937] in
                   FStar_Syntax_Subst.open_term uu____2936 phi in
                 match uu____2931 with
                 | (bvs, phi1) ->
                     let uu____2962 =
                       let uu____2963 = FStar_List.hd bvs in
                       FStar_Pervasives_Native.fst uu____2963 in
                     (uu____2962, phi1) in
               (match uu____2926 with
                | (bv1, phi1) ->
                    let uu____2982 =
                      let uu____2985 = FStar_Tactics_Types.goal_env g in
                      let uu____2986 =
                        let uu____2987 =
                          let uu____2990 =
                            let uu____2991 =
                              let uu____2998 =
                                FStar_Tactics_Types.goal_witness g in
                              (bv1, uu____2998) in
                            FStar_Syntax_Syntax.NT uu____2991 in
                          [uu____2990] in
                        FStar_Syntax_Subst.subst uu____2987 phi1 in
                      FStar_Tactics_Monad.mk_irrelevant_goal
                        "refine_intro refinement" uu____2985 uu____2986
                        g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label in
                    FStar_Tactics_Monad.bind uu____2982
                      (fun g2 ->
                         FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                           (fun uu____3007 ->
                              FStar_Tactics_Monad.add_goals [g1; g2])))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "refine_intro")
      uu____2878
let (__exact_now :
  Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun set_expected_typ ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let env1 =
             if set_expected_typ
             then
               let uu____3036 = FStar_Tactics_Types.goal_env goal in
               let uu____3037 = FStar_Tactics_Types.goal_type goal in
               FStar_TypeChecker_Env.set_expected_typ uu____3036 uu____3037
             else FStar_Tactics_Types.goal_env goal in
           let uu____3040 = __tc env1 t in
           FStar_Tactics_Monad.bind uu____3040
             (fun uu____3059 ->
                match uu____3059 with
                | (t1, typ, guard) ->
                    FStar_Tactics_Monad.mlog
                      (fun uu____3074 ->
                         let uu____3075 =
                           FStar_Syntax_Print.term_to_string typ in
                         let uu____3077 =
                           let uu____3079 = FStar_Tactics_Types.goal_env goal in
                           FStar_TypeChecker_Rel.guard_to_string uu____3079
                             guard in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3075 uu____3077)
                      (fun uu____3083 ->
                         let uu____3084 =
                           let uu____3087 = FStar_Tactics_Types.goal_env goal in
                           proc_guard "__exact typing" uu____3087 guard in
                         FStar_Tactics_Monad.bind uu____3084
                           (fun uu____3090 ->
                              FStar_Tactics_Monad.mlog
                                (fun uu____3094 ->
                                   let uu____3095 =
                                     FStar_Syntax_Print.term_to_string typ in
                                   let uu____3097 =
                                     let uu____3099 =
                                       FStar_Tactics_Types.goal_type goal in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3099 in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3095 uu____3097)
                                (fun uu____3103 ->
                                   let uu____3104 =
                                     let uu____3108 =
                                       FStar_Tactics_Types.goal_env goal in
                                     let uu____3109 =
                                       FStar_Tactics_Types.goal_type goal in
                                     do_unify uu____3108 typ uu____3109 in
                                   FStar_Tactics_Monad.bind uu____3104
                                     (fun b ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3119 =
                                             let uu____3126 =
                                               let uu____3132 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal in
                                               tts uu____3132 in
                                             let uu____3133 =
                                               FStar_Tactics_Types.goal_type
                                                 goal in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu____3126 typ uu____3133 in
                                           match uu____3119 with
                                           | (typ1, goalt) ->
                                               let uu____3142 =
                                                 let uu____3144 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 tts uu____3144 t1 in
                                               let uu____3145 =
                                                 let uu____3147 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 let uu____3148 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal in
                                                 tts uu____3147 uu____3148 in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu____3142 typ1 goalt
                                                 uu____3145)))))))
let (t_exact :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun try_refine ->
    fun set_expected_typ ->
      fun tm ->
        let uu____3174 =
          FStar_Tactics_Monad.mlog
            (fun uu____3179 ->
               let uu____3180 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3180)
            (fun uu____3185 ->
               let uu____3186 =
                 let uu____3193 = __exact_now set_expected_typ tm in
                 catch uu____3193 in
               FStar_Tactics_Monad.bind uu____3186
                 (fun uu___2_3202 ->
                    match uu___2_3202 with
                    | FStar_Util.Inr r -> FStar_Tactics_Monad.ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        FStar_Tactics_Monad.traise e
                    | FStar_Util.Inl e ->
                        FStar_Tactics_Monad.mlog
                          (fun uu____3213 ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3217 ->
                             let uu____3218 =
                               let uu____3225 =
                                 let uu____3228 =
                                   norm [FStar_Syntax_Embeddings.Delta] in
                                 FStar_Tactics_Monad.bind uu____3228
                                   (fun uu____3233 ->
                                      let uu____3234 = refine_intro () in
                                      FStar_Tactics_Monad.bind uu____3234
                                        (fun uu____3238 ->
                                           __exact_now set_expected_typ tm)) in
                               catch uu____3225 in
                             FStar_Tactics_Monad.bind uu____3218
                               (fun uu___1_3245 ->
                                  match uu___1_3245 with
                                  | FStar_Util.Inr r ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3254 ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____3257 ->
                                           FStar_Tactics_Monad.ret ())
                                  | FStar_Util.Inl uu____3258 ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3260 ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____3263 ->
                                           FStar_Tactics_Monad.traise e))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "exact") uu____3174
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
  fun only_match ->
    fun acc ->
      fun e ->
        fun ty1 ->
          fun ty2 ->
            let f = if only_match then do_match else do_unify in
            let uu____3364 = f e ty2 ty1 in
            FStar_Tactics_Monad.bind uu____3364
              (fun uu___3_3378 ->
                 if uu___3_3378
                 then FStar_Tactics_Monad.ret acc
                 else
                   (let uu____3398 = FStar_Syntax_Util.arrow_one ty1 in
                    match uu____3398 with
                    | FStar_Pervasives_Native.None ->
                        let uu____3419 = term_to_string e ty1 in
                        let uu____3421 = term_to_string e ty2 in
                        fail2 "Could not instantiate, %s to %s" uu____3419
                          uu____3421
                    | FStar_Pervasives_Native.Some (b, c) ->
                        let uu____3438 =
                          let uu____3440 = FStar_Syntax_Util.is_total_comp c in
                          Prims.op_Negation uu____3440 in
                        if uu____3438
                        then FStar_Tactics_Monad.fail "Codomain is effectful"
                        else
                          (let uu____3464 =
                             FStar_Tactics_Monad.new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           FStar_Tactics_Monad.bind uu____3464
                             (fun uu____3489 ->
                                match uu____3489 with
                                | (uvt, uv) ->
                                    FStar_Tactics_Monad.mlog
                                      (fun uu____3516 ->
                                         let uu____3517 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             uv in
                                         FStar_Util.print1
                                           "t_apply: generated uvar %s\n"
                                           uu____3517)
                                      (fun uu____3523 ->
                                         let typ =
                                           FStar_Syntax_Util.comp_result c in
                                         let typ' =
                                           FStar_Syntax_Subst.subst
                                             [FStar_Syntax_Syntax.NT
                                                ((FStar_Pervasives_Native.fst
                                                    b), uvt)] typ in
                                         __try_unify_by_application
                                           only_match
                                           ((uvt,
                                              (FStar_Pervasives_Native.snd b),
                                              uv) :: acc) e typ' ty2)))))
let (try_unify_by_application :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
            FStar_Syntax_Syntax.ctx_uvar) Prims.list FStar_Tactics_Monad.tac)
  =
  fun only_match ->
    fun e ->
      fun ty1 ->
        fun ty2 -> __try_unify_by_application only_match [] e ty1 ty2
let (t_apply :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun uopt ->
    fun only_match ->
      fun tm ->
        let uu____3613 =
          FStar_Tactics_Monad.mlog
            (fun uu____3618 ->
               let uu____3619 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____3619)
            (fun uu____3623 ->
               FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                 (fun goal ->
                    let e = FStar_Tactics_Types.goal_env goal in
                    FStar_Tactics_Monad.mlog
                      (fun uu____3632 ->
                         let uu____3633 =
                           FStar_Syntax_Print.term_to_string tm in
                         let uu____3635 =
                           FStar_Tactics_Printing.goal_to_string_verbose goal in
                         let uu____3637 =
                           FStar_TypeChecker_Env.print_gamma
                             e.FStar_TypeChecker_Env.gamma in
                         FStar_Util.print3
                           "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\n"
                           uu____3633 uu____3635 uu____3637)
                      (fun uu____3642 ->
                         let uu____3643 = __tc e tm in
                         FStar_Tactics_Monad.bind uu____3643
                           (fun uu____3664 ->
                              match uu____3664 with
                              | (tm1, typ, guard) ->
                                  let typ1 = bnorm e typ in
                                  let uu____3677 =
                                    let uu____3688 =
                                      FStar_Tactics_Types.goal_type goal in
                                    try_unify_by_application only_match e
                                      typ1 uu____3688 in
                                  FStar_Tactics_Monad.bind uu____3677
                                    (fun uvs ->
                                       FStar_Tactics_Monad.mlog
                                         (fun uu____3709 ->
                                            let uu____3710 =
                                              FStar_Common.string_of_list
                                                (fun uu____3722 ->
                                                   match uu____3722 with
                                                   | (t, uu____3731,
                                                      uu____3732) ->
                                                       FStar_Syntax_Print.term_to_string
                                                         t) uvs in
                                            FStar_Util.print1
                                              "t_apply: found args = %s\n"
                                              uu____3710)
                                         (fun uu____3740 ->
                                            let fix_qual q =
                                              match q with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.Meta
                                                  uu____3755) ->
                                                  FStar_Pervasives_Native.Some
                                                    (FStar_Syntax_Syntax.Implicit
                                                       false)
                                              | uu____3757 -> q in
                                            let w =
                                              FStar_List.fold_right
                                                (fun uu____3780 ->
                                                   fun w ->
                                                     match uu____3780 with
                                                     | (uvt, q, uu____3798)
                                                         ->
                                                         FStar_Syntax_Util.mk_app
                                                           w
                                                           [(uvt,
                                                              (fix_qual q))])
                                                uvs tm1 in
                                            let uvset =
                                              let uu____3830 =
                                                FStar_Syntax_Free.new_uv_set
                                                  () in
                                              FStar_List.fold_right
                                                (fun uu____3847 ->
                                                   fun s ->
                                                     match uu____3847 with
                                                     | (uu____3859,
                                                        uu____3860, uv) ->
                                                         let uu____3862 =
                                                           FStar_Syntax_Free.uvars
                                                             uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                         FStar_Util.set_union
                                                           s uu____3862) uvs
                                                uu____3830 in
                                            let free_in_some_goal uv =
                                              FStar_Util.set_mem uv uvset in
                                            let uu____3872 = solve' goal w in
                                            FStar_Tactics_Monad.bind
                                              uu____3872
                                              (fun uu____3877 ->
                                                 let uu____3878 =
                                                   FStar_Tactics_Monad.mapM
                                                     (fun uu____3895 ->
                                                        match uu____3895 with
                                                        | (uvt, q, uv) ->
                                                            let uu____3907 =
                                                              FStar_Syntax_Unionfind.find
                                                                uv.FStar_Syntax_Syntax.ctx_uvar_head in
                                                            (match uu____3907
                                                             with
                                                             | FStar_Pervasives_Native.Some
                                                                 uu____3912
                                                                 ->
                                                                 FStar_Tactics_Monad.ret
                                                                   ()
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 let uu____3913
                                                                   =
                                                                   uopt &&
                                                                    (free_in_some_goal
                                                                    uv) in
                                                                 if
                                                                   uu____3913
                                                                 then
                                                                   FStar_Tactics_Monad.ret
                                                                    ()
                                                                 else
                                                                   (let uu____3920
                                                                    =
                                                                    let uu____3923
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___605_3926
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___605_3926.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___605_3926.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___605_3926.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    [uu____3923] in
                                                                    FStar_Tactics_Monad.add_goals
                                                                    uu____3920)))
                                                     uvs in
                                                 FStar_Tactics_Monad.bind
                                                   uu____3878
                                                   (fun uu____3931 ->
                                                      proc_guard
                                                        "apply guard" e guard)))))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply") uu____3613
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c in
    let uu____3959 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid in
    if uu____3959
    then
      let uu____3968 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3983 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4036 -> failwith "apply_lemma: impossible: not a lemma" in
      match uu____3968 with
      | (pre, post) ->
          let post1 =
            let uu____4069 =
              let uu____4080 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
              [uu____4080] in
            FStar_Syntax_Util.mk_app post uu____4069 in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4111 =
         (FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)
           ||
           (FStar_Syntax_Util.is_ghost_effect
              ct.FStar_Syntax_Syntax.effect_name) in
       if uu____4111
       then
         let uu____4120 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ in
         FStar_Util.map_opt uu____4120
           (fun post -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
let rec fold_left :
  'a 'b .
    ('a -> 'b -> 'b FStar_Tactics_Monad.tac) ->
      'b -> 'a Prims.list -> 'b FStar_Tactics_Monad.tac
  =
  fun f ->
    fun e ->
      fun xs ->
        match xs with
        | [] -> FStar_Tactics_Monad.ret e
        | x::xs1 ->
            let uu____4199 = f x e in
            FStar_Tactics_Monad.bind uu____4199
              (fun e' -> fold_left f e' xs1)
let (apply_lemma : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun tm ->
    let uu____4214 =
      let uu____4217 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps ->
             FStar_Tactics_Monad.mlog
               (fun uu____4224 ->
                  let uu____4225 = FStar_Syntax_Print.term_to_string tm in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4225)
               (fun uu____4230 ->
                  let is_unit_t t =
                    let uu____4238 =
                      let uu____4239 = FStar_Syntax_Subst.compress t in
                      uu____4239.FStar_Syntax_Syntax.n in
                    match uu____4238 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4245 -> false in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                    (fun goal ->
                       let env1 = FStar_Tactics_Types.goal_env goal in
                       let uu____4252 = __tc env1 tm in
                       FStar_Tactics_Monad.bind uu____4252
                         (fun uu____4275 ->
                            match uu____4275 with
                            | (tm1, t, guard) ->
                                let uu____4287 =
                                  FStar_Syntax_Util.arrow_formals_comp t in
                                (match uu____4287 with
                                 | (bs, comp) ->
                                     let uu____4296 = lemma_or_sq comp in
                                     (match uu____4296 with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Tactics_Monad.fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre, post) ->
                                          let uu____4316 =
                                            fold_left
                                              (fun uu____4378 ->
                                                 fun uu____4379 ->
                                                   match (uu____4378,
                                                           uu____4379)
                                                   with
                                                   | ((b, aq),
                                                      (uvs, imps, subst)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst
                                                           b.FStar_Syntax_Syntax.sort in
                                                       let uu____4530 =
                                                         is_unit_t b_t in
                                                       if uu____4530
                                                       then
                                                         FStar_All.pipe_left
                                                           FStar_Tactics_Monad.ret
                                                           (((FStar_Syntax_Util.exp_unit,
                                                               aq) :: uvs),
                                                             imps,
                                                             ((FStar_Syntax_Syntax.NT
                                                                 (b,
                                                                   FStar_Syntax_Util.exp_unit))
                                                             :: subst))
                                                       else
                                                         (let uu____4653 =
                                                            FStar_Tactics_Monad.new_uvar
                                                              "apply_lemma"
                                                              env1 b_t in
                                                          FStar_Tactics_Monad.bind
                                                            uu____4653
                                                            (fun uu____4690
                                                               ->
                                                               match uu____4690
                                                               with
                                                               | (t1, u) ->
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
                                                                    subst)))))
                                              ([], [], []) bs in
                                          FStar_Tactics_Monad.bind uu____4316
                                            (fun uu____4877 ->
                                               match uu____4877 with
                                               | (uvs, implicits1, subst) ->
                                                   let implicits2 =
                                                     FStar_List.rev
                                                       implicits1 in
                                                   let uvs1 =
                                                     FStar_List.rev uvs in
                                                   let pre1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst pre in
                                                   let post1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst post in
                                                   let post_u =
                                                     env1.FStar_TypeChecker_Env.universe_of
                                                       env1 post1 in
                                                   let uu____4966 =
                                                     let uu____4970 =
                                                       FStar_Syntax_Util.mk_squash
                                                         post_u post1 in
                                                     let uu____4971 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal in
                                                     do_unify env1 uu____4970
                                                       uu____4971 in
                                                   FStar_Tactics_Monad.bind
                                                     uu____4966
                                                     (fun b ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____4983 =
                                                            let uu____4990 =
                                                              FStar_Syntax_Util.mk_squash
                                                                post_u post1 in
                                                            let uu____4991 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal in
                                                            FStar_TypeChecker_Err.print_discrepancy
                                                              (tts env1)
                                                              uu____4990
                                                              uu____4991 in
                                                          match uu____4983
                                                          with
                                                          | (post2, goalt) ->
                                                              let uu____5000
                                                                =
                                                                tts env1 tm1 in
                                                              fail3
                                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                uu____5000
                                                                post2 goalt
                                                        else
                                                          (let uu____5005 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit in
                                                           FStar_Tactics_Monad.bind
                                                             uu____5005
                                                             (fun uu____5013
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____5041
                                                                    =
                                                                    let uu____5044
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1 in
                                                                    FStar_Util.set_elements
                                                                    uu____5044 in
                                                                    FStar_List.map
                                                                    (fun x ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5041 in
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun u ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars in
                                                                let appears
                                                                  uv goals =
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun g' ->
                                                                    let uu____5082
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g' in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5082)
                                                                    goals in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____5099
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1 in
                                                                  match uu____5099
                                                                  with
                                                                  | (hd,
                                                                    uu____5118)
                                                                    ->
                                                                    (match 
                                                                    hd.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,
                                                                    uu____5145)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5162
                                                                    -> false) in
                                                                let uu____5164
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    implicits2
                                                                    (
                                                                    FStar_Tactics_Monad.mapM
                                                                    (fun imp
                                                                    ->
                                                                    let uu____5205
                                                                    = imp in
                                                                    match uu____5205
                                                                    with
                                                                    | 
                                                                    (term,
                                                                    ctx_uvar)
                                                                    ->
                                                                    let uu____5216
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____5216
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu____5238)
                                                                    ->
                                                                    let uu____5263
                                                                    =
                                                                    let uu____5264
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd in
                                                                    uu____5264.FStar_Syntax_Syntax.n in
                                                                    (match uu____5263
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,
                                                                    uu____5272)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___726_5292
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___726_5292.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___726_5292.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___726_5292.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___726_5292.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    FStar_Tactics_Monad.ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5295
                                                                    ->
                                                                    FStar_Tactics_Monad.mlog
                                                                    (fun
                                                                    uu____5301
                                                                    ->
                                                                    let uu____5302
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                                                                    let uu____5304
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5302
                                                                    uu____5304)
                                                                    (fun
                                                                    uu____5310
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env1
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ in
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
                                                                    ctx_uvar in
                                                                    let uu____5322
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5320
                                                                    uu____5322
                                                                    else
                                                                    "apply_lemma solved arg" in
                                                                    proc_guard
                                                                    uu____5316
                                                                    env1
                                                                    g_typ in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5313
                                                                    (fun
                                                                    uu____5331
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    [])))))) in
                                                                FStar_Tactics_Monad.bind
                                                                  uu____5164
                                                                  (fun
                                                                    sub_goals
                                                                    ->
                                                                    let sub_goals1
                                                                    =
                                                                    FStar_List.flatten
                                                                    sub_goals in
                                                                    let rec filter'
                                                                    f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____5395
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____5395
                                                                    then
                                                                    let uu____5400
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____5400
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g ->
                                                                    fun goals
                                                                    ->
                                                                    let uu____5415
                                                                    =
                                                                    let uu____5417
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g in
                                                                    checkone
                                                                    uu____5417
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____5415)
                                                                    sub_goals1 in
                                                                    let uu____5418
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    env1
                                                                    guard in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5418
                                                                    (fun
                                                                    uu____5425
                                                                    ->
                                                                    let pre_u
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 pre1 in
                                                                    let uu____5427
                                                                    =
                                                                    let uu____5430
                                                                    =
                                                                    let uu____5432
                                                                    =
                                                                    let uu____5434
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre_u
                                                                    pre1 in
                                                                    istrivial
                                                                    env1
                                                                    uu____5434 in
                                                                    Prims.op_Negation
                                                                    uu____5432 in
                                                                    if
                                                                    uu____5430
                                                                    then
                                                                    FStar_Tactics_Monad.add_irrelevant_goal
                                                                    goal
                                                                    "apply_lemma precondition"
                                                                    env1 pre1
                                                                    else
                                                                    FStar_Tactics_Monad.ret
                                                                    () in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5427
                                                                    (fun
                                                                    uu____5442
                                                                    ->
                                                                    FStar_Tactics_Monad.add_goals
                                                                    sub_goals2))))))))))))) in
      focus uu____4217 in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply_lemma")
      uu____4214
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____5466 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____5466 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,
         uu____5476::(e1, FStar_Pervasives_Native.None)::(e2,
                                                          FStar_Pervasives_Native.None)::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l, uu____5536::uu____5537::(e1, uu____5539)::(e2, uu____5541)::[]))
        when FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5618 ->
        let uu____5621 = FStar_Syntax_Util.unb2t typ in
        (match uu____5621 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____5635 = FStar_Syntax_Util.head_and_args t in
             (match uu____5635 with
              | (hd, args) ->
                  let uu____5684 =
                    let uu____5699 =
                      let uu____5700 = FStar_Syntax_Subst.compress hd in
                      uu____5700.FStar_Syntax_Syntax.n in
                    (uu____5699, args) in
                  (match uu____5684 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,
                      (uu____5720, FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____5721))::(e1,
                                                                    FStar_Pervasives_Native.None)::
                      (e2, FStar_Pervasives_Native.None)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____5789 -> FStar_Pervasives_Native.None)))
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____5826 = destruct_eq' typ in
    match uu____5826 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None ->
        let uu____5856 = FStar_Syntax_Util.un_squash typ in
        (match uu____5856 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar ->
    fun e ->
      let rec aux e1 =
        let uu____5925 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____5925 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv', e') ->
            let uu____5960 = FStar_Syntax_Syntax.bv_eq bvar bv' in
            if uu____5960
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____5985 = aux e' in
               FStar_Util.map_opt uu____5985
                 (fun uu____6016 ->
                    match uu____6016 with
                    | (e'', bv, bvs) -> (e'', bv, (bv' :: bvs)))) in
      let uu____6042 = aux e in
      FStar_Util.map_opt uu____6042
        (fun uu____6073 ->
           match uu____6073 with
           | (e', bv, bvs) -> (e', bv, (FStar_List.rev bvs)))
let (push_bvs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env)
  =
  fun e ->
    fun bvs ->
      FStar_List.fold_left
        (fun e1 -> fun b -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
let (subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Tactics_Types.goal ->
        (FStar_Syntax_Syntax.bv * FStar_Tactics_Types.goal)
          FStar_Pervasives_Native.option FStar_Tactics_Monad.tac)
  =
  fun b1 ->
    fun b2 ->
      fun g ->
        let uu____6150 =
          let uu____6161 = FStar_Tactics_Types.goal_env g in
          split_env b1 uu____6161 in
        match uu____6150 with
        | FStar_Pervasives_Native.Some (e0, b11, bvs) ->
            let bs =
              FStar_List.map FStar_Syntax_Syntax.mk_binder (b11 :: bvs) in
            let t = FStar_Tactics_Types.goal_type g in
            let uu____6201 =
              let uu____6214 = FStar_Syntax_Subst.close_binders bs in
              let uu____6223 = FStar_Syntax_Subst.close bs t in
              (uu____6214, uu____6223) in
            (match uu____6201 with
             | (bs', t') ->
                 let bs'1 =
                   let uu____6267 = FStar_Syntax_Syntax.mk_binder b2 in
                   let uu____6274 = FStar_List.tail bs' in uu____6267 ::
                     uu____6274 in
                 let uu____6295 = FStar_Syntax_Subst.open_term bs'1 t' in
                 (match uu____6295 with
                  | (bs'', t'') ->
                      let b21 =
                        let uu____6311 = FStar_List.hd bs'' in
                        FStar_Pervasives_Native.fst uu____6311 in
                      let new_env =
                        let uu____6327 =
                          FStar_List.map FStar_Pervasives_Native.fst bs'' in
                        push_bvs e0 uu____6327 in
                      let uu____6338 =
                        FStar_Tactics_Monad.new_uvar "subst_goal" new_env t'' in
                      FStar_Tactics_Monad.bind uu____6338
                        (fun uu____6362 ->
                           match uu____6362 with
                           | (uvt, uv) ->
                               let goal' =
                                 FStar_Tactics_Types.mk_goal new_env uv
                                   g.FStar_Tactics_Types.opts
                                   g.FStar_Tactics_Types.is_guard
                                   g.FStar_Tactics_Types.label in
                               let sol =
                                 let uu____6381 =
                                   FStar_Syntax_Util.abs bs'' uvt
                                     FStar_Pervasives_Native.None in
                                 let uu____6384 =
                                   FStar_List.map
                                     (fun uu____6405 ->
                                        match uu____6405 with
                                        | (bv, q) ->
                                            let uu____6418 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                bv in
                                            FStar_Syntax_Syntax.as_arg
                                              uu____6418) bs in
                                 FStar_Syntax_Util.mk_app uu____6381
                                   uu____6384 in
                               let uu____6419 = set_solution g sol in
                               FStar_Tactics_Monad.bind uu____6419
                                 (fun uu____6429 ->
                                    FStar_Tactics_Monad.ret
                                      (FStar_Pervasives_Native.Some
                                         (b21, goal'))))))
        | FStar_Pervasives_Native.None ->
            FStar_Tactics_Monad.ret FStar_Pervasives_Native.None
let (rewrite : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun h ->
    let uu____6468 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____6476 = h in
           match uu____6476 with
           | (bv, uu____6480) ->
               FStar_Tactics_Monad.mlog
                 (fun uu____6488 ->
                    let uu____6489 = FStar_Syntax_Print.bv_to_string bv in
                    let uu____6491 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6489
                      uu____6491)
                 (fun uu____6496 ->
                    let uu____6497 =
                      let uu____6508 = FStar_Tactics_Types.goal_env goal in
                      split_env bv uu____6508 in
                    match uu____6497 with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.fail
                          "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                        let uu____6535 =
                          let uu____6542 =
                            whnf e0 bv1.FStar_Syntax_Syntax.sort in
                          destruct_eq uu____6542 in
                        (match uu____6535 with
                         | FStar_Pervasives_Native.Some (x, e) ->
                             let uu____6551 =
                               let uu____6552 = FStar_Syntax_Subst.compress x in
                               uu____6552.FStar_Syntax_Syntax.n in
                             (match uu____6551 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                  let t = FStar_Tactics_Types.goal_type goal in
                                  let bs =
                                    FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder bvs in
                                  let uu____6579 =
                                    let uu____6584 =
                                      FStar_Syntax_Subst.close_binders bs in
                                    let uu____6585 =
                                      FStar_Syntax_Subst.close bs t in
                                    (uu____6584, uu____6585) in
                                  (match uu____6579 with
                                   | (bs', t') ->
                                       let uu____6590 =
                                         let uu____6595 =
                                           FStar_Syntax_Subst.subst_binders s
                                             bs' in
                                         let uu____6596 =
                                           FStar_Syntax_Subst.subst s t in
                                         (uu____6595, uu____6596) in
                                       (match uu____6590 with
                                        | (bs'1, t'1) ->
                                            let uu____6601 =
                                              FStar_Syntax_Subst.open_term
                                                bs'1 t'1 in
                                            (match uu____6601 with
                                             | (bs'', t'') ->
                                                 let new_env =
                                                   let uu____6611 =
                                                     let uu____6614 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         bs'' in
                                                     bv1 :: uu____6614 in
                                                   push_bvs e0 uu____6611 in
                                                 let uu____6625 =
                                                   FStar_Tactics_Monad.new_uvar
                                                     "rewrite" new_env t'' in
                                                 FStar_Tactics_Monad.bind
                                                   uu____6625
                                                   (fun uu____6643 ->
                                                      match uu____6643 with
                                                      | (uvt, uv) ->
                                                          let goal' =
                                                            FStar_Tactics_Types.mk_goal
                                                              new_env uv
                                                              goal.FStar_Tactics_Types.opts
                                                              goal.FStar_Tactics_Types.is_guard
                                                              goal.FStar_Tactics_Types.label in
                                                          let sol =
                                                            let uu____6656 =
                                                              FStar_Syntax_Util.abs
                                                                bs'' uvt
                                                                FStar_Pervasives_Native.None in
                                                            let uu____6659 =
                                                              FStar_List.map
                                                                (fun
                                                                   uu____6680
                                                                   ->
                                                                   match uu____6680
                                                                   with
                                                                   | 
                                                                   (bv2,
                                                                    uu____6688)
                                                                    ->
                                                                    let uu____6693
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv2 in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____6693)
                                                                bs in
                                                            FStar_Syntax_Util.mk_app
                                                              uu____6656
                                                              uu____6659 in
                                                          let uu____6694 =
                                                            set_solution goal
                                                              sol in
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
                               "Not an equality hypothesis"))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rewrite") uu____6468
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac)
  =
  fun b ->
    fun s ->
      let uu____6731 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____6753 = b in
             match uu____6753 with
             | (bv, q) ->
                 let bv' =
                   let uu____6769 =
                     let uu___904_6770 = bv in
                     let uu____6771 =
                       let uu____6772 =
                         let uu____6778 =
                           FStar_Ident.range_of_id
                             bv.FStar_Syntax_Syntax.ppname in
                         (s, uu____6778) in
                       FStar_Ident.mk_ident uu____6772 in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6771;
                       FStar_Syntax_Syntax.index =
                         (uu___904_6770.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___904_6770.FStar_Syntax_Syntax.sort)
                     } in
                   FStar_Syntax_Syntax.freshen_bv uu____6769 in
                 let uu____6780 = subst_goal bv bv' goal in
                 FStar_Tactics_Monad.bind uu____6780
                   (fun uu___4_6802 ->
                      match uu___4_6802 with
                      | FStar_Pervasives_Native.None ->
                          FStar_Tactics_Monad.fail
                            "binder not found in environment"
                      | FStar_Pervasives_Native.Some (bv'1, goal1) ->
                          let uu____6834 =
                            FStar_Tactics_Monad.replace_cur goal1 in
                          FStar_Tactics_Monad.bind uu____6834
                            (fun uu____6844 ->
                               FStar_Tactics_Monad.ret (bv'1, q)))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rename_to")
        uu____6731
let (binder_retype :
  FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let uu____6880 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____6889 = b in
           match uu____6889 with
           | (bv, uu____6893) ->
               let uu____6898 =
                 let uu____6909 = FStar_Tactics_Types.goal_env goal in
                 split_env bv uu____6909 in
               (match uu____6898 with
                | FStar_Pervasives_Native.None ->
                    FStar_Tactics_Monad.fail
                      "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                    let uu____6936 = FStar_Syntax_Util.type_u () in
                    (match uu____6936 with
                     | (ty, u) ->
                         let uu____6945 =
                           FStar_Tactics_Monad.new_uvar "binder_retype" e0 ty in
                         FStar_Tactics_Monad.bind uu____6945
                           (fun uu____6964 ->
                              match uu____6964 with
                              | (t', u_t') ->
                                  let bv'' =
                                    let uu___931_6974 = bv1 in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___931_6974.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___931_6974.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    } in
                                  let s =
                                    let uu____6978 =
                                      let uu____6979 =
                                        let uu____6986 =
                                          FStar_Syntax_Syntax.bv_to_name bv'' in
                                        (bv1, uu____6986) in
                                      FStar_Syntax_Syntax.NT uu____6979 in
                                    [uu____6978] in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1 ->
                                         let uu___936_6998 = b1 in
                                         let uu____6999 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___936_6998.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___936_6998.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6999
                                         }) bvs in
                                  let env' = push_bvs e0 (bv'' :: bvs1) in
                                  FStar_Tactics_Monad.bind
                                    FStar_Tactics_Monad.dismiss
                                    (fun uu____7006 ->
                                       let new_goal =
                                         let uu____7008 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env' in
                                         let uu____7009 =
                                           let uu____7010 =
                                             FStar_Tactics_Types.goal_type
                                               goal in
                                           FStar_Syntax_Subst.subst s
                                             uu____7010 in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____7008 uu____7009 in
                                       let uu____7011 =
                                         FStar_Tactics_Monad.add_goals
                                           [new_goal] in
                                       FStar_Tactics_Monad.bind uu____7011
                                         (fun uu____7016 ->
                                            let uu____7017 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t' in
                                            FStar_Tactics_Monad.add_irrelevant_goal
                                              goal "binder_retype equation"
                                              e0 uu____7017)))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "binder_retype")
      uu____6880
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    fun b ->
      let uu____7043 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____7052 = b in
             match uu____7052 with
             | (bv, uu____7056) ->
                 let uu____7061 =
                   let uu____7072 = FStar_Tactics_Types.goal_env goal in
                   split_env bv uu____7072 in
                 (match uu____7061 with
                  | FStar_Pervasives_Native.None ->
                      FStar_Tactics_Monad.fail
                        "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                      let steps =
                        let uu____7102 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____7102 in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort in
                      let bv' =
                        let uu___957_7107 = bv1 in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___957_7107.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___957_7107.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        } in
                      let env' = push_bvs e0 (bv' :: bvs) in
                      let uu____7109 =
                        FStar_Tactics_Types.goal_with_env goal env' in
                      FStar_Tactics_Monad.replace_cur uu____7109)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_binder_type")
        uu____7043
let (revert : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7122 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____7128 =
           let uu____7135 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____7135 in
         match uu____7128 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x, env') ->
             let typ' =
               let uu____7152 =
                 let uu____7155 = FStar_Tactics_Types.goal_type goal in
                 FStar_Syntax_Syntax.mk_Total uu____7155 in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____7152 in
             let uu____7170 = FStar_Tactics_Monad.new_uvar "revert" env' typ' in
             FStar_Tactics_Monad.bind uu____7170
               (fun uu____7186 ->
                  match uu____7186 with
                  | (r, u_r) ->
                      let uu____7195 =
                        let uu____7198 =
                          let uu____7199 =
                            let uu____7200 =
                              let uu____7209 =
                                FStar_Syntax_Syntax.bv_to_name x in
                              FStar_Syntax_Syntax.as_arg uu____7209 in
                            [uu____7200] in
                          let uu____7226 =
                            let uu____7227 =
                              FStar_Tactics_Types.goal_type goal in
                            uu____7227.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.mk_Tm_app r uu____7199
                            uu____7226 in
                        set_solution goal uu____7198 in
                      FStar_Tactics_Monad.bind uu____7195
                        (fun uu____7232 ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                               goal.FStar_Tactics_Types.label in
                           FStar_Tactics_Monad.replace_cur g)))
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv ->
    fun t ->
      let uu____7246 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____7246
let (clear : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let bv = FStar_Pervasives_Native.fst b in
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____7267 ->
              let uu____7268 = FStar_Syntax_Print.binder_to_string b in
              let uu____7270 =
                let uu____7272 =
                  let uu____7274 =
                    let uu____7283 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.all_binders uu____7283 in
                  FStar_All.pipe_right uu____7274 FStar_List.length in
                FStar_All.pipe_right uu____7272 FStar_Util.string_of_int in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____7268 uu____7270)
           (fun uu____7304 ->
              let uu____7305 =
                let uu____7316 = FStar_Tactics_Types.goal_env goal in
                split_env bv uu____7316 in
              match uu____7305 with
              | FStar_Pervasives_Native.None ->
                  FStar_Tactics_Monad.fail
                    "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e', bv1, bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> FStar_Tactics_Monad.ret ()
                    | bv'::bvs2 ->
                        let uu____7361 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort in
                        if uu____7361
                        then
                          let uu____7366 =
                            let uu____7368 =
                              FStar_Syntax_Print.bv_to_string bv' in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____7368 in
                          FStar_Tactics_Monad.fail uu____7366
                        else check bvs2 in
                  let uu____7373 =
                    let uu____7375 = FStar_Tactics_Types.goal_type goal in
                    free_in bv1 uu____7375 in
                  if uu____7373
                  then
                    FStar_Tactics_Monad.fail
                      "Cannot clear; binder present in goal"
                  else
                    (let uu____7382 = check bvs in
                     FStar_Tactics_Monad.bind uu____7382
                       (fun uu____7388 ->
                          let env' = push_bvs e' bvs in
                          let uu____7390 =
                            let uu____7397 =
                              FStar_Tactics_Types.goal_type goal in
                            FStar_Tactics_Monad.new_uvar "clear.witness" env'
                              uu____7397 in
                          FStar_Tactics_Monad.bind uu____7390
                            (fun uu____7407 ->
                               match uu____7407 with
                               | (ut, uvar_ut) ->
                                   let uu____7416 = set_solution goal ut in
                                   FStar_Tactics_Monad.bind uu____7416
                                     (fun uu____7421 ->
                                        let uu____7422 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label in
                                        FStar_Tactics_Monad.replace_cur
                                          uu____7422))))))
let (clear_top : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7430 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____7436 =
           let uu____7443 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____7443 in
         match uu____7436 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x, uu____7452) ->
             let uu____7457 = FStar_Syntax_Syntax.mk_binder x in
             clear uu____7457)
let (prune : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____7477 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____7477 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (addns : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____7498 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____7498 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (_trefl :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun l ->
    fun r ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____7518 =
             let uu____7522 = FStar_Tactics_Types.goal_env g in
             do_unify uu____7522 l r in
           FStar_Tactics_Monad.bind uu____7518
             (fun b ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____7533 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7533 l in
                   let r1 =
                     let uu____7535 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7535 r in
                   let uu____7536 =
                     let uu____7540 = FStar_Tactics_Types.goal_env g in
                     do_unify uu____7540 l1 r1 in
                   FStar_Tactics_Monad.bind uu____7536
                     (fun b1 ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____7550 =
                             let uu____7557 =
                               let uu____7563 =
                                 FStar_Tactics_Types.goal_env g in
                               tts uu____7563 in
                             FStar_TypeChecker_Err.print_discrepancy
                               uu____7557 l1 r1 in
                           match uu____7550 with
                           | (ls, rs) ->
                               fail2 "not a trivial equality ((%s) vs (%s))"
                                 ls rs)))))
let (trefl : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7580 ->
    let uu____7583 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____7591 =
             let uu____7598 =
               let uu____7599 = FStar_Tactics_Types.goal_env g in
               let uu____7600 = FStar_Tactics_Types.goal_type g in
               whnf uu____7599 uu____7600 in
             destruct_eq uu____7598 in
           match uu____7591 with
           | FStar_Pervasives_Native.Some (l, r) -> _trefl l r
           | FStar_Pervasives_Native.None ->
               let uu____7613 =
                 let uu____7615 = FStar_Tactics_Types.goal_env g in
                 let uu____7616 = FStar_Tactics_Types.goal_type g in
                 tts uu____7615 uu____7616 in
               fail1 "not an equality (%s)" uu____7613) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "trefl") uu____7583
let (dup : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7630 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let env1 = FStar_Tactics_Types.goal_env g in
         let uu____7638 =
           let uu____7645 = FStar_Tactics_Types.goal_type g in
           FStar_Tactics_Monad.new_uvar "dup" env1 uu____7645 in
         FStar_Tactics_Monad.bind uu____7638
           (fun uu____7655 ->
              match uu____7655 with
              | (u, u_uvar) ->
                  let g' =
                    let uu___1043_7665 = g in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1043_7665.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1043_7665.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1043_7665.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1043_7665.FStar_Tactics_Types.label)
                    } in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____7669 ->
                       let t_eq =
                         let uu____7671 =
                           let uu____7672 = FStar_Tactics_Types.goal_type g in
                           env1.FStar_TypeChecker_Env.universe_of env1
                             uu____7672 in
                         let uu____7673 = FStar_Tactics_Types.goal_type g in
                         let uu____7674 = FStar_Tactics_Types.goal_witness g in
                         FStar_Syntax_Util.mk_eq2 uu____7671 uu____7673 u
                           uu____7674 in
                       let uu____7675 =
                         FStar_Tactics_Monad.add_irrelevant_goal g
                           "dup equation" env1 t_eq in
                       FStar_Tactics_Monad.bind uu____7675
                         (fun uu____7681 ->
                            let uu____7682 =
                              FStar_Tactics_Monad.add_goals [g'] in
                            FStar_Tactics_Monad.bind uu____7682
                              (fun uu____7686 -> FStar_Tactics_Monad.ret ())))))
let longest_prefix :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list -> ('a Prims.list * 'a Prims.list * 'a Prims.list)
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        let rec aux acc l11 l21 =
          match (l11, l21) with
          | (x::xs, y::ys) ->
              let uu____7812 = f x y in
              if uu____7812 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____7835 -> (acc, l11, l21) in
        let uu____7850 = aux [] l1 l2 in
        match uu____7850 with | (pr, t1, t2) -> ((FStar_List.rev pr), t1, t2)
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal ->
      FStar_Tactics_Types.goal FStar_Tactics_Monad.tac)
  =
  fun g1 ->
    fun g2 ->
      let close_forall_no_univs bs f =
        FStar_List.fold_right
          (fun b ->
             fun f1 ->
               FStar_Syntax_Util.mk_forall_no_univ
                 (FStar_Pervasives_Native.fst b) f1) bs f in
      let uu____7956 = FStar_Tactics_Types.get_phi g1 in
      match uu____7956 with
      | FStar_Pervasives_Native.None ->
          FStar_Tactics_Monad.fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____7963 = FStar_Tactics_Types.get_phi g2 in
          (match uu____7963 with
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let uu____7976 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2) in
               (match uu____7976 with
                | (gamma, r1, r2) ->
                    let t1 =
                      let uu____8007 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1) in
                      close_forall_no_univs uu____8007 phi1 in
                    let t2 =
                      let uu____8017 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2) in
                      close_forall_no_univs uu____8017 phi2 in
                    let uu____8026 =
                      set_solution g1 FStar_Syntax_Util.exp_unit in
                    FStar_Tactics_Monad.bind uu____8026
                      (fun uu____8031 ->
                         let uu____8032 =
                           set_solution g2 FStar_Syntax_Util.exp_unit in
                         FStar_Tactics_Monad.bind uu____8032
                           (fun uu____8039 ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2 in
                              let nenv =
                                let uu___1095_8044 =
                                  FStar_Tactics_Types.goal_env g1 in
                                let uu____8045 =
                                  FStar_Util.smap_create (Prims.of_int (100)) in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1095_8044.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1095_8044.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1095_8044.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1095_8044.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____8045;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1095_8044.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1095_8044.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1095_8044.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1095_8044.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1095_8044.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1095_8044.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1095_8044.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1095_8044.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1095_8044.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1095_8044.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1095_8044.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1095_8044.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1095_8044.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1095_8044.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1095_8044.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1095_8044.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1095_8044.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1095_8044.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1095_8044.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1095_8044.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1095_8044.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1095_8044.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1095_8044.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1095_8044.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1095_8044.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1095_8044.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1095_8044.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1095_8044.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1095_8044.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1095_8044.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1095_8044.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1095_8044.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1095_8044.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1095_8044.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1095_8044.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1095_8044.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1095_8044.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1095_8044.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1095_8044.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1095_8044.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___1095_8044.FStar_TypeChecker_Env.enable_defer_to_tac)
                                } in
                              let uu____8049 =
                                FStar_Tactics_Monad.mk_irrelevant_goal
                                  "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label in
                              FStar_Tactics_Monad.bind uu____8049
                                (fun goal ->
                                   FStar_Tactics_Monad.mlog
                                     (fun uu____8059 ->
                                        let uu____8060 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g1 in
                                        let uu____8062 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g2 in
                                        let uu____8064 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            goal in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____8060 uu____8062 uu____8064)
                                     (fun uu____8068 ->
                                        FStar_Tactics_Monad.ret goal))))))
let (join : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____8076 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____8092 =
               FStar_Tactics_Monad.set
                 (let uu___1110_8097 = ps in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1110_8097.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1110_8097.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1110_8097.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1110_8097.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1110_8097.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1110_8097.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1110_8097.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1110_8097.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1110_8097.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1110_8097.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1110_8097.FStar_Tactics_Types.local_state)
                  }) in
             FStar_Tactics_Monad.bind uu____8092
               (fun uu____8100 ->
                  let uu____8101 = join_goals g1 g2 in
                  FStar_Tactics_Monad.bind uu____8101
                    (fun g12 -> FStar_Tactics_Monad.add_goals [g12]))
         | uu____8106 -> FStar_Tactics_Monad.fail "join: less than 2 goals")
let (set_options : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    let uu____8122 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           FStar_Options.push ();
           (let uu____8135 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
            FStar_Options.set uu____8135);
           (let res = FStar_Options.set_options s in
            let opts' = FStar_Options.peek () in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success ->
                 let g' =
                   let uu___1121_8142 = g in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1121_8142.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1121_8142.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1121_8142.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1121_8142.FStar_Tactics_Types.label)
                   } in
                 FStar_Tactics_Monad.replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "set_options")
      uu____8122
let (top_env : unit -> env FStar_Tactics_Monad.tac) =
  fun uu____8159 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_All.pipe_left FStar_Tactics_Monad.ret
           ps.FStar_Tactics_Types.main_context)
let (lax_on : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____8174 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let uu____8182 =
           (FStar_Options.lax ()) ||
             (let uu____8185 = FStar_Tactics_Types.goal_env g in
              uu____8185.FStar_TypeChecker_Env.lax) in
         FStar_Tactics_Monad.ret uu____8182)
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun tm ->
      let uu____8202 =
        FStar_Tactics_Monad.mlog
          (fun uu____8207 ->
             let uu____8208 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "unquote: tm = %s\n" uu____8208)
          (fun uu____8212 ->
             FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
               (fun goal ->
                  let env1 =
                    let uu____8218 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.set_expected_typ uu____8218 ty in
                  let uu____8219 = __tc_ghost env1 tm in
                  FStar_Tactics_Monad.bind uu____8219
                    (fun uu____8238 ->
                       match uu____8238 with
                       | (tm1, typ, guard) ->
                           FStar_Tactics_Monad.mlog
                             (fun uu____8252 ->
                                let uu____8253 =
                                  FStar_Syntax_Print.term_to_string tm1 in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____8253)
                             (fun uu____8257 ->
                                FStar_Tactics_Monad.mlog
                                  (fun uu____8260 ->
                                     let uu____8261 =
                                       FStar_Syntax_Print.term_to_string typ in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____8261)
                                  (fun uu____8266 ->
                                     let uu____8267 =
                                       proc_guard "unquote" env1 guard in
                                     FStar_Tactics_Monad.bind uu____8267
                                       (fun uu____8272 ->
                                          FStar_Tactics_Monad.ret tm1)))))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unquote") uu____8202
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun ty ->
      let uu____8297 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> FStar_Tactics_Monad.ret ty1
        | FStar_Pervasives_Native.None ->
            let uu____8303 =
              let uu____8310 =
                let uu____8311 = FStar_Syntax_Util.type_u () in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8311 in
              FStar_Tactics_Monad.new_uvar "uvar_env.2" env1 uu____8310 in
            FStar_Tactics_Monad.bind uu____8303
              (fun uu____8328 ->
                 match uu____8328 with
                 | (typ, uvar_typ) -> FStar_Tactics_Monad.ret typ) in
      FStar_Tactics_Monad.bind uu____8297
        (fun typ ->
           let uu____8340 = FStar_Tactics_Monad.new_uvar "uvar_env" env1 typ in
           FStar_Tactics_Monad.bind uu____8340
             (fun uu____8355 ->
                match uu____8355 with
                | (t, uvar_t) -> FStar_Tactics_Monad.ret t))
let (unshelve : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____8374 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           let env1 = ps.FStar_Tactics_Types.main_context in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8393 -> g.FStar_Tactics_Types.opts
             | uu____8396 -> FStar_Options.peek () in
           let uu____8399 = FStar_Syntax_Util.head_and_args t in
           match uu____8399 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar, uu____8419);
                FStar_Syntax_Syntax.pos = uu____8420;
                FStar_Syntax_Syntax.vars = uu____8421;_},
              uu____8422) ->
               let env2 =
                 let uu___1175_8464 = env1 in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1175_8464.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1175_8464.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1175_8464.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1175_8464.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1175_8464.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1175_8464.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1175_8464.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1175_8464.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1175_8464.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1175_8464.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1175_8464.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1175_8464.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1175_8464.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1175_8464.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1175_8464.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1175_8464.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___1175_8464.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1175_8464.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1175_8464.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1175_8464.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1175_8464.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1175_8464.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1175_8464.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1175_8464.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1175_8464.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1175_8464.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1175_8464.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1175_8464.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1175_8464.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1175_8464.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1175_8464.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1175_8464.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1175_8464.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1175_8464.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1175_8464.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___1175_8464.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1175_8464.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1175_8464.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1175_8464.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1175_8464.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1175_8464.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1175_8464.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1175_8464.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1175_8464.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1175_8464.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (uu___1175_8464.FStar_TypeChecker_Env.enable_defer_to_tac)
                 } in
               let g =
                 FStar_Tactics_Types.mk_goal env2 ctx_uvar opts false "" in
               let uu____8468 = let uu____8471 = bnorm_goal g in [uu____8471] in
               FStar_Tactics_Monad.add_goals uu____8468
           | uu____8472 -> FStar_Tactics_Monad.fail "not a uvar") in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unshelve") uu____8374
let (tac_and :
  Prims.bool FStar_Tactics_Monad.tac ->
    Prims.bool FStar_Tactics_Monad.tac -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let comp =
        FStar_Tactics_Monad.bind t1
          (fun b ->
             let uu____8534 = if b then t2 else FStar_Tactics_Monad.ret false in
             FStar_Tactics_Monad.bind uu____8534
               (fun b' ->
                  if b'
                  then FStar_Tactics_Monad.ret b'
                  else FStar_Tactics_Monad.fail "")) in
      let uu____8560 = trytac comp in
      FStar_Tactics_Monad.bind uu____8560
        (fun uu___5_8572 ->
           match uu___5_8572 with
           | FStar_Pervasives_Native.Some (true) ->
               FStar_Tactics_Monad.ret true
           | FStar_Pervasives_Native.Some (false) -> failwith "impossible"
           | FStar_Pervasives_Native.None -> FStar_Tactics_Monad.ret false)
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu____8614 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu____8622 = __tc e t1 in
               FStar_Tactics_Monad.bind uu____8622
                 (fun uu____8643 ->
                    match uu____8643 with
                    | (t11, ty1, g1) ->
                        let uu____8656 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu____8656
                          (fun uu____8677 ->
                             match uu____8677 with
                             | (t21, ty2, g2) ->
                                 let uu____8690 =
                                   proc_guard "unify_env g1" e g1 in
                                 FStar_Tactics_Monad.bind uu____8690
                                   (fun uu____8697 ->
                                      let uu____8698 =
                                        proc_guard "unify_env g2" e g2 in
                                      FStar_Tactics_Monad.bind uu____8698
                                        (fun uu____8706 ->
                                           let uu____8707 =
                                             do_unify e ty1 ty2 in
                                           let uu____8711 =
                                             do_unify e t11 t21 in
                                           tac_and uu____8707 uu____8711))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unify_env")
          uu____8614
let (launch_process :
  Prims.string ->
    Prims.string Prims.list ->
      Prims.string -> Prims.string FStar_Tactics_Monad.tac)
  =
  fun prog ->
    fun args ->
      fun input ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____8759 ->
             let uu____8760 = FStar_Options.unsafe_tactic_exec () in
             if uu____8760
             then
               let s =
                 FStar_Util.run_process "tactic_launch" prog args
                   (FStar_Pervasives_Native.Some input) in
               FStar_Tactics_Monad.ret s
             else
               FStar_Tactics_Monad.fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
let (fresh_bv_named :
  Prims.string ->
    FStar_Reflection_Data.typ ->
      FStar_Syntax_Syntax.bv FStar_Tactics_Monad.tac)
  =
  fun nm ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
        (fun uu____8794 ->
           let uu____8795 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t in
           FStar_Tactics_Monad.ret uu____8795)
let (change : FStar_Reflection_Data.typ -> unit FStar_Tactics_Monad.tac) =
  fun ty ->
    let uu____8806 =
      FStar_Tactics_Monad.mlog
        (fun uu____8811 ->
           let uu____8812 = FStar_Syntax_Print.term_to_string ty in
           FStar_Util.print1 "change: ty = %s\n" uu____8812)
        (fun uu____8816 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                let uu____8820 =
                  let uu____8829 = FStar_Tactics_Types.goal_env g in
                  __tc uu____8829 ty in
                FStar_Tactics_Monad.bind uu____8820
                  (fun uu____8841 ->
                     match uu____8841 with
                     | (ty1, uu____8851, guard) ->
                         let uu____8853 =
                           let uu____8856 = FStar_Tactics_Types.goal_env g in
                           proc_guard "change" uu____8856 guard in
                         FStar_Tactics_Monad.bind uu____8853
                           (fun uu____8860 ->
                              let uu____8861 =
                                let uu____8865 =
                                  FStar_Tactics_Types.goal_env g in
                                let uu____8866 =
                                  FStar_Tactics_Types.goal_type g in
                                do_unify uu____8865 uu____8866 ty1 in
                              FStar_Tactics_Monad.bind uu____8861
                                (fun bb ->
                                   if bb
                                   then
                                     let uu____8875 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1 in
                                     FStar_Tactics_Monad.replace_cur
                                       uu____8875
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops] in
                                      let ng =
                                        let uu____8882 =
                                          FStar_Tactics_Types.goal_env g in
                                        let uu____8883 =
                                          FStar_Tactics_Types.goal_type g in
                                        normalize steps uu____8882 uu____8883 in
                                      let nty =
                                        let uu____8885 =
                                          FStar_Tactics_Types.goal_env g in
                                        normalize steps uu____8885 ty1 in
                                      let uu____8886 =
                                        let uu____8890 =
                                          FStar_Tactics_Types.goal_env g in
                                        do_unify uu____8890 ng nty in
                                      FStar_Tactics_Monad.bind uu____8886
                                        (fun b ->
                                           if b
                                           then
                                             let uu____8899 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1 in
                                             FStar_Tactics_Monad.replace_cur
                                               uu____8899
                                           else
                                             FStar_Tactics_Monad.fail
                                               "not convertible"))))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "change") uu____8806
let failwhen :
  'a .
    Prims.bool ->
      Prims.string ->
        (unit -> 'a FStar_Tactics_Monad.tac) -> 'a FStar_Tactics_Monad.tac
  =
  fun b ->
    fun msg -> fun k -> if b then FStar_Tactics_Monad.fail msg else k ()
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list
      FStar_Tactics_Monad.tac)
  =
  fun s_tm ->
    let uu____8973 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____8991 =
             let uu____9000 = FStar_Tactics_Types.goal_env g in
             __tc uu____9000 s_tm in
           FStar_Tactics_Monad.bind uu____8991
             (fun uu____9018 ->
                match uu____9018 with
                | (s_tm1, s_ty, guard) ->
                    let uu____9036 =
                      let uu____9039 = FStar_Tactics_Types.goal_env g in
                      proc_guard "destruct" uu____9039 guard in
                    FStar_Tactics_Monad.bind uu____9036
                      (fun uu____9053 ->
                         let s_ty1 =
                           let uu____9055 = FStar_Tactics_Types.goal_env g in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant] uu____9055
                             s_ty in
                         let uu____9056 =
                           let uu____9071 = FStar_Syntax_Util.unrefine s_ty1 in
                           FStar_Syntax_Util.head_and_args' uu____9071 in
                         match uu____9056 with
                         | (h, args) ->
                             let uu____9102 =
                               let uu____9109 =
                                 let uu____9110 =
                                   FStar_Syntax_Subst.compress h in
                                 uu____9110.FStar_Syntax_Syntax.n in
                               match uu____9109 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   FStar_Tactics_Monad.ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____9125;
                                      FStar_Syntax_Syntax.vars = uu____9126;_},
                                    us)
                                   -> FStar_Tactics_Monad.ret (fv, us)
                               | uu____9136 ->
                                   FStar_Tactics_Monad.fail
                                     "type is not an fv" in
                             FStar_Tactics_Monad.bind uu____9102
                               (fun uu____9157 ->
                                  match uu____9157 with
                                  | (fv, a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv in
                                      let uu____9173 =
                                        let uu____9176 =
                                          FStar_Tactics_Types.goal_env g in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____9176 t_lid in
                                      (match uu____9173 with
                                       | FStar_Pervasives_Native.None ->
                                           FStar_Tactics_Monad.fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid, t_us, t_ps, t_ty, mut,
                                                 c_lids)
                                                ->
                                                let erasable =
                                                  FStar_Syntax_Util.has_attribute
                                                    se.FStar_Syntax_Syntax.sigattrs
                                                    FStar_Parser_Const.erasable_attr in
                                                let uu____9217 =
                                                  erasable &&
                                                    (let uu____9220 =
                                                       FStar_Tactics_Types.is_irrelevant
                                                         g in
                                                     Prims.op_Negation
                                                       uu____9220) in
                                                failwhen uu____9217
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____9230 ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____9243 ->
                                                          let uu____9244 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty in
                                                          match uu____9244
                                                          with
                                                          | (t_ps1, t_ty1) ->
                                                              let uu____9259
                                                                =
                                                                FStar_Tactics_Monad.mapM
                                                                  (fun c_lid
                                                                    ->
                                                                    let uu____9287
                                                                    =
                                                                    let uu____9290
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____9290
                                                                    c_lid in
                                                                    match uu____9287
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
                                                                    (_c_lid,
                                                                    c_us,
                                                                    c_ty,
                                                                    _t_lid,
                                                                    nparam,
                                                                    mut1) ->
                                                                    let fv1 =
                                                                    FStar_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    (FStar_Pervasives_Native.Some
                                                                    FStar_Syntax_Syntax.Data_ctor) in
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_us) <>
                                                                    (FStar_List.length
                                                                    c_us))
                                                                    "t_us don't match?"
                                                                    (fun
                                                                    uu____9367
                                                                    ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty in
                                                                    let uu____9372
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1) in
                                                                    match uu____9372
                                                                    with
                                                                    | 
                                                                    (c_us1,
                                                                    c_ty2) ->
                                                                    let uu____9395
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2 in
                                                                    (match uu____9395
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    comp) ->
                                                                    let uu____9414
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname in
                                                                    let ppname1
                                                                    =
                                                                    let uu____9437
                                                                    =
                                                                    let uu____9443
                                                                    =
                                                                    let uu____9445
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    ppname in
                                                                    Prims.op_Hat
                                                                    "a"
                                                                    uu____9445 in
                                                                    let uu____9448
                                                                    =
                                                                    FStar_Ident.range_of_id
                                                                    ppname in
                                                                    (uu____9443,
                                                                    uu____9448) in
                                                                    FStar_Ident.mk_ident
                                                                    uu____9437 in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    (let uu___1303_9452
                                                                    = bv in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1303_9452.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (uu___1303_9452.FStar_Syntax_Syntax.sort)
                                                                    }) in
                                                                    let bs' =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9478
                                                                    ->
                                                                    match uu____9478
                                                                    with
                                                                    | 
                                                                    (bv, aq)
                                                                    ->
                                                                    let uu____9497
                                                                    =
                                                                    rename_bv
                                                                    bv in
                                                                    (uu____9497,
                                                                    aq)) bs in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun
                                                                    uu____9522
                                                                    ->
                                                                    fun
                                                                    uu____9523
                                                                    ->
                                                                    match 
                                                                    (uu____9522,
                                                                    uu____9523)
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9549),
                                                                    (bv',
                                                                    uu____9551))
                                                                    ->
                                                                    let uu____9572
                                                                    =
                                                                    let uu____9579
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv' in
                                                                    (bv,
                                                                    uu____9579) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____9572)
                                                                    bs bs' in
                                                                    let uu____9584
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs' in
                                                                    let uu____9593
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst
                                                                    comp in
                                                                    (uu____9584,
                                                                    uu____9593) in
                                                                    (match uu____9414
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    comp1) ->
                                                                    let uu____9640
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    bs1 in
                                                                    (match uu____9640
                                                                    with
                                                                    | 
                                                                    (d_ps,
                                                                    bs2) ->
                                                                    let uu____9713
                                                                    =
                                                                    let uu____9715
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1 in
                                                                    Prims.op_Negation
                                                                    uu____9715 in
                                                                    failwhen
                                                                    uu____9713
                                                                    "not total?"
                                                                    (fun
                                                                    uu____9734
                                                                    ->
                                                                    let mk_pat
                                                                    p =
                                                                    {
                                                                    FStar_Syntax_Syntax.v
                                                                    = p;
                                                                    FStar_Syntax_Syntax.p
                                                                    =
                                                                    (s_tm1.FStar_Syntax_Syntax.pos)
                                                                    } in
                                                                    let is_imp
                                                                    uu___6_9751
                                                                    =
                                                                    match uu___6_9751
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____9755)
                                                                    -> true
                                                                    | 
                                                                    uu____9758
                                                                    -> false in
                                                                    let uu____9762
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args in
                                                                    match uu____9762
                                                                    with
                                                                    | 
                                                                    (a_ps,
                                                                    a_is) ->
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_ps) <>
                                                                    (FStar_List.length
                                                                    d_ps))
                                                                    "params not match?"
                                                                    (fun
                                                                    uu____9898
                                                                    ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9960
                                                                    ->
                                                                    match uu____9960
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9980),
                                                                    (t,
                                                                    uu____9982))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps in
                                                                    let bs3 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs2 in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____10052
                                                                    ->
                                                                    match uu____10052
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____10079),
                                                                    (t,
                                                                    uu____10081))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (bv, t))),
                                                                    true))
                                                                    d_ps_a_ps in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____10140
                                                                    ->
                                                                    match uu____10140
                                                                    with
                                                                    | 
                                                                    (bv, aq)
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    aq))) bs3 in
                                                                    let subpats
                                                                    =
                                                                    FStar_List.append
                                                                    subpats_1
                                                                    subpats_2 in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    subpats)) in
                                                                    let env1
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    let cod =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g in
                                                                    let equ =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1
                                                                    s_ty1 in
                                                                    let uu____10195
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1362_10219
                                                                    = env1 in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.erasable_types_tab);
                                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___1362_10219.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                    }) s_ty1
                                                                    pat in
                                                                    match uu____10195
                                                                    with
                                                                    | 
                                                                    (uu____10233,
                                                                    uu____10234,
                                                                    uu____10235,
                                                                    uu____10236,
                                                                    pat_t,
                                                                    uu____10238,
                                                                    _guard_pat,
                                                                    _erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____10252
                                                                    =
                                                                    let uu____10253
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____10253 in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____10252 in
                                                                    let cod1
                                                                    =
                                                                    let uu____10258
                                                                    =
                                                                    let uu____10267
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b in
                                                                    [uu____10267] in
                                                                    let uu____10286
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____10258
                                                                    uu____10286 in
                                                                    let nty =
                                                                    let uu____10292
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu____10292 in
                                                                    let uu____10295
                                                                    =
                                                                    FStar_Tactics_Monad.new_uvar
                                                                    "destruct branch"
                                                                    env1 nty in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10295
                                                                    (fun
                                                                    uu____10325
                                                                    ->
                                                                    match uu____10325
                                                                    with
                                                                    | 
                                                                    (uvt, uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env1 uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false
                                                                    g.FStar_Tactics_Types.label in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs3 in
                                                                    let brt1
                                                                    =
                                                                    let uu____10352
                                                                    =
                                                                    let uu____10363
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit in
                                                                    [uu____10363] in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____10352 in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1) in
                                                                    let uu____10399
                                                                    =
                                                                    let uu____10410
                                                                    =
                                                                    let uu____10415
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs3) in
                                                                    (fv1,
                                                                    uu____10415) in
                                                                    (g', br,
                                                                    uu____10410) in
                                                                    FStar_Tactics_Monad.ret
                                                                    uu____10399)))))))
                                                                    | 
                                                                    uu____10436
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids in
                                                              FStar_Tactics_Monad.bind
                                                                uu____9259
                                                                (fun goal_brs
                                                                   ->
                                                                   let uu____10486
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs in
                                                                   match uu____10486
                                                                   with
                                                                   | 
                                                                   (goals,
                                                                    brs,
                                                                    infos) ->
                                                                    let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    s_tm1.FStar_Syntax_Syntax.pos in
                                                                    let uu____10559
                                                                    =
                                                                    solve' g
                                                                    w in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10559
                                                                    (fun
                                                                    uu____10570
                                                                    ->
                                                                    let uu____10571
                                                                    =
                                                                    FStar_Tactics_Monad.add_goals
                                                                    goals in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10571
                                                                    (fun
                                                                    uu____10581
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    infos)))))
                                            | uu____10588 ->
                                                FStar_Tactics_Monad.fail
                                                  "not an inductive type")))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "destruct") uu____8973
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____10637::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____10667 = init xs in x :: uu____10667
let rec (inspect :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Tactics_Monad.tac)
  =
  fun t ->
    let uu____10680 =
      let uu____10683 = top_env () in
      FStar_Tactics_Monad.bind uu____10683
        (fun e ->
           let t1 = FStar_Syntax_Util.unascribe t in
           let t2 = FStar_Syntax_Util.un_uinst t1 in
           let t3 = FStar_Syntax_Util.unlazy_emb t2 in
           match t3.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_meta (t4, uu____10699) -> inspect t4
           | FStar_Syntax_Syntax.Tm_name bv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Var bv)
           | FStar_Syntax_Syntax.Tm_bvar bv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_BVar bv)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_FVar fv)
           | FStar_Syntax_Syntax.Tm_app (hd, []) ->
               failwith "empty arguments on Tm_app"
           | FStar_Syntax_Syntax.Tm_app (hd, args) ->
               let uu____10765 = last args in
               (match uu____10765 with
                | (a, q) ->
                    let q' = FStar_Reflection_Basic.inspect_aqual q in
                    let uu____10795 =
                      let uu____10796 =
                        let uu____10801 =
                          let uu____10802 = init args in
                          FStar_Syntax_Syntax.mk_Tm_app hd uu____10802
                            t3.FStar_Syntax_Syntax.pos in
                        (uu____10801, (a, q')) in
                      FStar_Reflection_Data.Tv_App uu____10796 in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10795)
           | FStar_Syntax_Syntax.Tm_abs ([], uu____10813, uu____10814) ->
               failwith "empty arguments on Tm_abs"
           | FStar_Syntax_Syntax.Tm_abs (bs, t4, k) ->
               let uu____10867 = FStar_Syntax_Subst.open_term bs t4 in
               (match uu____10867 with
                | (bs1, t5) ->
                    (match bs1 with
                     | [] -> failwith "impossible"
                     | b::bs2 ->
                         let uu____10909 =
                           let uu____10910 =
                             let uu____10915 = FStar_Syntax_Util.abs bs2 t5 k in
                             (b, uu____10915) in
                           FStar_Reflection_Data.Tv_Abs uu____10910 in
                         FStar_All.pipe_left FStar_Tactics_Monad.ret
                           uu____10909))
           | FStar_Syntax_Syntax.Tm_type uu____10918 ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Type ())
           | FStar_Syntax_Syntax.Tm_arrow ([], k) ->
               failwith "empty binders on arrow"
           | FStar_Syntax_Syntax.Tm_arrow uu____10943 ->
               let uu____10958 = FStar_Syntax_Util.arrow_one t3 in
               (match uu____10958 with
                | FStar_Pervasives_Native.Some (b, c) ->
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Arrow (b, c))
                | FStar_Pervasives_Native.None -> failwith "impossible")
           | FStar_Syntax_Syntax.Tm_refine (bv, t4) ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____10989 = FStar_Syntax_Subst.open_term [b] t4 in
               (match uu____10989 with
                | (b', t5) ->
                    let b1 =
                      match b' with
                      | b'1::[] -> b'1
                      | uu____11042 -> failwith "impossible" in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Refine
                         ((FStar_Pervasives_Native.fst b1), t5)))
           | FStar_Syntax_Syntax.Tm_constant c ->
               let uu____11055 =
                 let uu____11056 = FStar_Reflection_Basic.inspect_const c in
                 FStar_Reflection_Data.Tv_Const uu____11056 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11055
           | FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
               let uu____11077 =
                 let uu____11078 =
                   let uu____11083 =
                     let uu____11084 =
                       FStar_Syntax_Unionfind.uvar_id
                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                     FStar_BigInt.of_int_fs uu____11084 in
                   (uu____11083, (ctx_u, s)) in
                 FStar_Reflection_Data.Tv_Uvar uu____11078 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11077
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____11124 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let b = FStar_Syntax_Syntax.mk_binder bv in
                      let uu____11129 = FStar_Syntax_Subst.open_term [b] t21 in
                      (match uu____11129 with
                       | (bs, t22) ->
                           let b1 =
                             match bs with
                             | b1::[] -> b1
                             | uu____11182 ->
                                 failwith
                                   "impossible: open_term returned different amount of binders" in
                           FStar_All.pipe_left FStar_Tactics_Monad.ret
                             (FStar_Reflection_Data.Tv_Let
                                (false, (lb.FStar_Syntax_Syntax.lbattrs),
                                  (FStar_Pervasives_Native.fst b1),
                                  (lb.FStar_Syntax_Syntax.lbdef), t22))))
           | FStar_Syntax_Syntax.Tm_let ((true, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____11226 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let uu____11230 =
                        FStar_Syntax_Subst.open_let_rec [lb] t21 in
                      (match uu____11230 with
                       | (lbs, t22) ->
                           (match lbs with
                            | lb1::[] ->
                                (match lb1.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____11250 ->
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
                            | uu____11258 ->
                                failwith
                                  "impossible: open_term returned different amount of binders")))
           | FStar_Syntax_Syntax.Tm_match (t4, brs) ->
               let rec inspect_pat p =
                 match p.FStar_Syntax_Syntax.v with
                 | FStar_Syntax_Syntax.Pat_constant c ->
                     let uu____11313 = FStar_Reflection_Basic.inspect_const c in
                     FStar_Reflection_Data.Pat_Constant uu____11313
                 | FStar_Syntax_Syntax.Pat_cons (fv, ps) ->
                     let uu____11334 =
                       let uu____11346 =
                         FStar_List.map
                           (fun uu____11370 ->
                              match uu____11370 with
                              | (p1, b) ->
                                  let uu____11391 = inspect_pat p1 in
                                  (uu____11391, b)) ps in
                       (fv, uu____11346) in
                     FStar_Reflection_Data.Pat_Cons uu____11334
                 | FStar_Syntax_Syntax.Pat_var bv ->
                     FStar_Reflection_Data.Pat_Var bv
                 | FStar_Syntax_Syntax.Pat_wild bv ->
                     FStar_Reflection_Data.Pat_Wild bv
                 | FStar_Syntax_Syntax.Pat_dot_term (bv, t5) ->
                     FStar_Reflection_Data.Pat_Dot_Term (bv, t5) in
               let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
               let brs2 =
                 FStar_List.map
                   (fun uu___7_11487 ->
                      match uu___7_11487 with
                      | (pat, uu____11509, t5) ->
                          let uu____11527 = inspect_pat pat in
                          (uu____11527, t5)) brs1 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Match (t4, brs2))
           | FStar_Syntax_Syntax.Tm_unknown ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 FStar_Reflection_Data.Tv_Unknown
           | uu____11536 ->
               ((let uu____11538 =
                   let uu____11544 =
                     let uu____11546 = FStar_Syntax_Print.tag_of_term t3 in
                     let uu____11548 = term_to_string e t3 in
                     FStar_Util.format2
                       "inspect: outside of expected syntax (%s, %s)\n"
                       uu____11546 uu____11548 in
                   (FStar_Errors.Warning_CantInspect, uu____11544) in
                 FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos
                   uu____11538);
                FStar_All.pipe_left FStar_Tactics_Monad.ret
                  FStar_Reflection_Data.Tv_Unknown)) in
    FStar_Tactics_Monad.wrap_err "inspect" uu____10680
let (pack :
  FStar_Reflection_Data.term_view ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun tv ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____11566 = FStar_Syntax_Syntax.bv_to_name bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11566
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____11570 = FStar_Syntax_Syntax.bv_to_tm bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11570
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____11574 = FStar_Syntax_Syntax.fv_to_tm fv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11574
    | FStar_Reflection_Data.Tv_App (l, (r, q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q in
        let uu____11581 = FStar_Syntax_Util.mk_app l [(r, q')] in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11581
    | FStar_Reflection_Data.Tv_Abs (b, t) ->
        let uu____11606 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11606
    | FStar_Reflection_Data.Tv_Arrow (b, c) ->
        let uu____11623 = FStar_Syntax_Util.arrow [b] c in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11623
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left FStar_Tactics_Monad.ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv, t) ->
        let uu____11642 = FStar_Syntax_Util.refine bv t in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11642
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____11646 =
          let uu____11647 =
            let uu____11648 = FStar_Reflection_Basic.pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____11648 in
          FStar_Syntax_Syntax.mk uu____11647 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11646
    | FStar_Reflection_Data.Tv_Uvar (_u, ctx_u_s) ->
        let uu____11653 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11653
    | FStar_Reflection_Data.Tv_Let (false, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____11667 =
          let uu____11668 =
            let uu____11669 =
              let uu____11683 =
                let uu____11686 =
                  let uu____11687 = FStar_Syntax_Syntax.mk_binder bv in
                  [uu____11687] in
                FStar_Syntax_Subst.close uu____11686 t2 in
              ((false, [lb]), uu____11683) in
            FStar_Syntax_Syntax.Tm_let uu____11669 in
          FStar_Syntax_Syntax.mk uu____11668 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11667
    | FStar_Reflection_Data.Tv_Let (true, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____11732 = FStar_Syntax_Subst.close_let_rec [lb] t2 in
        (match uu____11732 with
         | (lbs, body) ->
             let uu____11747 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Range.dummyRange in
             FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11747)
    | FStar_Reflection_Data.Tv_Match (t, brs) ->
        let wrap v =
          {
            FStar_Syntax_Syntax.v = v;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____11784 =
                let uu____11785 = FStar_Reflection_Basic.pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____11785 in
              FStar_All.pipe_left wrap uu____11784
          | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
              let uu____11802 =
                let uu____11803 =
                  let uu____11817 =
                    FStar_List.map
                      (fun uu____11841 ->
                         match uu____11841 with
                         | (p1, b) ->
                             let uu____11856 = pack_pat p1 in
                             (uu____11856, b)) ps in
                  (fv, uu____11817) in
                FStar_Syntax_Syntax.Pat_cons uu____11803 in
              FStar_All.pipe_left wrap uu____11802
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv, t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1)) in
        let brs1 =
          FStar_List.map
            (fun uu___8_11904 ->
               match uu___8_11904 with
               | (pat, t1) ->
                   let uu____11921 = pack_pat pat in
                   (uu____11921, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        let uu____11969 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11969
    | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
        let uu____11997 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11997
    | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
        let uu____12043 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____12043
    | FStar_Reflection_Data.Tv_Unknown ->
        let uu____12082 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____12082
let (lget :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun k ->
      let uu____12102 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps ->
             let uu____12108 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k in
             match uu____12108 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lget") uu____12102
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun _ty ->
    fun k ->
      fun t ->
        let uu____12142 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let ps1 =
                 let uu___1667_12149 = ps in
                 let uu____12150 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___1667_12149.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___1667_12149.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___1667_12149.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___1667_12149.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___1667_12149.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___1667_12149.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___1667_12149.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___1667_12149.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___1667_12149.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___1667_12149.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___1667_12149.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____12150
                 } in
               FStar_Tactics_Monad.set ps1) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lset") uu____12142
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env1 ->
    fun typ ->
      let uu____12177 =
        FStar_TypeChecker_Env.new_implicit_var_aux "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env1 typ
          FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None in
      match uu____12177 with
      | (u, ctx_uvars, g_u) ->
          let uu____12210 = FStar_List.hd ctx_uvars in
          (match uu____12210 with
           | (ctx_uvar, uu____12224) ->
               let g =
                 let uu____12226 = FStar_Options.peek () in
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar uu____12226 false
                   "" in
               (g, g_u))
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env1 ->
    let uu____12235 = FStar_TypeChecker_Env.clear_expected_typ env1 in
    match uu____12235 with
    | (env2, uu____12243) ->
        let env3 =
          let uu___1684_12249 = env2 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1684_12249.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1684_12249.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1684_12249.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1684_12249.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1684_12249.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1684_12249.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1684_12249.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1684_12249.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1684_12249.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1684_12249.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___1684_12249.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1684_12249.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1684_12249.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1684_12249.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1684_12249.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1684_12249.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1684_12249.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1684_12249.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1684_12249.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1684_12249.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1684_12249.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1684_12249.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1684_12249.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1684_12249.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1684_12249.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1684_12249.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1684_12249.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1684_12249.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1684_12249.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1684_12249.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1684_12249.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1684_12249.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1684_12249.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1684_12249.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1684_12249.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1684_12249.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1684_12249.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1684_12249.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1684_12249.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1684_12249.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1684_12249.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1684_12249.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1684_12249.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1684_12249.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1684_12249.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1684_12249.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        let env4 =
          let uu___1687_12252 = env3 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1687_12252.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1687_12252.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1687_12252.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1687_12252.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1687_12252.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1687_12252.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1687_12252.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1687_12252.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1687_12252.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1687_12252.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1687_12252.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1687_12252.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1687_12252.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1687_12252.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1687_12252.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1687_12252.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1687_12252.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1687_12252.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1687_12252.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1687_12252.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1687_12252.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1687_12252.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1687_12252.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___1687_12252.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1687_12252.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1687_12252.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1687_12252.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1687_12252.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1687_12252.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1687_12252.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1687_12252.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1687_12252.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1687_12252.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1687_12252.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1687_12252.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1687_12252.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1687_12252.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1687_12252.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1687_12252.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1687_12252.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1687_12252.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1687_12252.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1687_12252.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1687_12252.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1687_12252.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1687_12252.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        env4
let (proofstate_of_goals :
  FStar_Range.range ->
    env ->
      FStar_Tactics_Types.goal Prims.list ->
        FStar_TypeChecker_Common.implicit Prims.list ->
          FStar_Tactics_Types.proofstate)
  =
  fun rng ->
    fun env1 ->
      fun goals ->
        fun imps ->
          let env2 = tac_env env1 in
          let ps =
            let uu____12285 =
              FStar_TypeChecker_Env.debug env2
                (FStar_Options.Other "TacVerbose") in
            let uu____12288 = FStar_Util.psmap_empty () in
            {
              FStar_Tactics_Types.main_context = env2;
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
              FStar_Tactics_Types.tac_verb_dbg = uu____12285;
              FStar_Tactics_Types.local_state = uu____12288
            } in
          ps
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env1 ->
      fun typ ->
        let env2 = tac_env env1 in
        let uu____12314 = goal_of_goal_ty env2 typ in
        match uu____12314 with
        | (g, g_u) ->
            let ps =
              proofstate_of_goals rng env2 [g]
                g_u.FStar_TypeChecker_Common.implicits in
            let uu____12326 = FStar_Tactics_Types.goal_witness g in
            (ps, uu____12326)
let (goal_of_implicit :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicit -> FStar_Tactics_Types.goal)
  =
  fun env1 ->
    fun i ->
      let uu____12338 = FStar_Options.peek () in
      FStar_Tactics_Types.mk_goal
        (let uu___1706_12341 = env1 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1706_12341.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1706_12341.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1706_12341.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             ((i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1706_12341.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1706_12341.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1706_12341.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1706_12341.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1706_12341.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1706_12341.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1706_12341.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1706_12341.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1706_12341.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1706_12341.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1706_12341.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1706_12341.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1706_12341.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___1706_12341.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___1706_12341.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___1706_12341.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___1706_12341.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1706_12341.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1706_12341.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1706_12341.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1706_12341.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1706_12341.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1706_12341.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1706_12341.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1706_12341.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1706_12341.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1706_12341.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1706_12341.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1706_12341.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1706_12341.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1706_12341.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1706_12341.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1706_12341.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1706_12341.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___1706_12341.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___1706_12341.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1706_12341.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1706_12341.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1706_12341.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1706_12341.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1706_12341.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1706_12341.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___1706_12341.FStar_TypeChecker_Env.enable_defer_to_tac)
         }) i.FStar_TypeChecker_Common.imp_uvar uu____12338 false
        i.FStar_TypeChecker_Common.imp_reason
let (proofstate_of_all_implicits :
  FStar_Range.range ->
    env ->
      implicits ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env1 ->
      fun imps ->
        let env2 = tac_env env1 in
        let goals = FStar_List.map (goal_of_implicit env2) imps in
        let w =
          let uu____12368 = FStar_List.hd goals in
          FStar_Tactics_Types.goal_witness uu____12368 in
        let ps =
          let uu____12370 =
            FStar_TypeChecker_Env.debug env2
              (FStar_Options.Other "TacVerbose") in
          let uu____12373 = FStar_Util.psmap_empty () in
          {
            FStar_Tactics_Types.main_context = env2;
            FStar_Tactics_Types.all_implicits = imps;
            FStar_Tactics_Types.goals = goals;
            FStar_Tactics_Types.smt_goals = [];
            FStar_Tactics_Types.depth = Prims.int_zero;
            FStar_Tactics_Types.__dump =
              (fun ps ->
                 fun msg -> FStar_Tactics_Printing.do_dump_proofstate ps msg);
            FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
            FStar_Tactics_Types.entry_range = rng;
            FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
            FStar_Tactics_Types.freshness = Prims.int_zero;
            FStar_Tactics_Types.tac_verb_dbg = uu____12370;
            FStar_Tactics_Types.local_state = uu____12373
          } in
        (ps, w)