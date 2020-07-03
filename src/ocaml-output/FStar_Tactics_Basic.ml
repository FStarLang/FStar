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
    let uu____58 =
      let uu____59 = FStar_Tactics_Types.goal_env g in
      let uu____60 = FStar_Tactics_Types.goal_type g in
      bnorm uu____59 uu____60 in
    FStar_Tactics_Types.goal_with_type g uu____58
let (tacprint : Prims.string -> unit) =
  fun s -> FStar_Util.print1 "TAC>> %s\n" s
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      let uu____76 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____76
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        let uu____92 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____92
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        fun z ->
          let uu____113 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____113
let (print : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    (let uu____124 =
       let uu____125 = FStar_Options.silent () in Prims.op_Negation uu____125 in
     if uu____124 then tacprint msg else ());
    FStar_Tactics_Monad.ret ()
let (debugging : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____133 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let uu____139 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac") in
         FStar_Tactics_Monad.ret uu____139)
let (dump : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst = FStar_TypeChecker_Cfg.psc_subst psc in
         (let uu____157 = FStar_Tactics_Types.subst_proof_state subst ps in
          FStar_Tactics_Printing.do_dump_proofstate uu____157 msg);
         FStar_Tactics_Result.Success ((), ps))
let fail1 :
  'uuuuuu164 .
    Prims.string -> Prims.string -> 'uuuuuu164 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      let uu____177 = FStar_Util.format1 msg x in
      FStar_Tactics_Monad.fail uu____177
let fail2 :
  'uuuuuu186 .
    Prims.string ->
      Prims.string -> Prims.string -> 'uuuuuu186 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        let uu____204 = FStar_Util.format2 msg x y in
        FStar_Tactics_Monad.fail uu____204
let fail3 :
  'uuuuuu215 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> 'uuuuuu215 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          let uu____238 = FStar_Util.format3 msg x y z in
          FStar_Tactics_Monad.fail uu____238
let fail4 :
  'uuuuuu251 .
    Prims.string ->
      Prims.string ->
        Prims.string ->
          Prims.string -> Prims.string -> 'uuuuuu251 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          fun w ->
            let uu____279 = FStar_Util.format4 msg x y z w in
            FStar_Tactics_Monad.fail uu____279
let catch :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (Prims.exn, 'a) FStar_Util.either FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____312 = FStar_Tactics_Monad.run t ps in
         match uu____312 with
         | FStar_Tactics_Result.Success (a1, q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a1), q))
         | FStar_Tactics_Result.Failed (m, q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___68_336 = ps in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___68_336.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___68_336.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___68_336.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___68_336.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___68_336.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___68_336.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___68_336.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___68_336.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___68_336.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___68_336.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___68_336.FStar_Tactics_Types.local_state)
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
         let uu____374 = FStar_Tactics_Monad.run t ps in
         match uu____374 with
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
    let uu____421 = catch t in
    FStar_Tactics_Monad.bind uu____421
      (fun r ->
         match r with
         | FStar_Util.Inr v ->
             FStar_Tactics_Monad.ret (FStar_Pervasives_Native.Some v)
         | FStar_Util.Inl uu____448 ->
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
           (fun uu___94_479 ->
              match () with
              | () ->
                  let uu____484 = trytac t in
                  FStar_Tactics_Monad.run uu____484 ps) ()
         with
         | FStar_Errors.Err (uu____500, msg) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____504 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____509, msg, uu____511) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____514 ->
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
        (let uu____539 =
           FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "1346") in
         if uu____539
         then
           let uu____540 = FStar_Syntax_Print.term_to_string t1 in
           let uu____541 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____540
             uu____541
         else ());
        (try
           (fun uu___114_548 ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env1 t1 t2 in
                  ((let uu____555 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "1346") in
                    if uu____555
                    then
                      let uu____556 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env1) res in
                      let uu____557 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____558 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____556
                        uu____557 uu____558
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____563 =
                          FStar_Tactics_Monad.add_implicits
                            g.FStar_TypeChecker_Common.implicits in
                        FStar_Tactics_Monad.bind uu____563
                          (fun uu____567 -> FStar_Tactics_Monad.ret true))))
             ()
         with
         | FStar_Errors.Err (uu____574, msg) ->
             FStar_Tactics_Monad.mlog
               (fun uu____577 ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____579 -> FStar_Tactics_Monad.ret false)
         | FStar_Errors.Error (uu____580, msg, r) ->
             FStar_Tactics_Monad.mlog
               (fun uu____585 ->
                  let uu____586 = FStar_Range.string_of_range r in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____586)
               (fun uu____588 -> FStar_Tactics_Monad.ret false))
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____611 ->
             (let uu____613 =
                FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "1346") in
              if uu____613
              then
                (FStar_Options.push ();
                 (let uu____615 =
                    FStar_Options.set_options
                      "--debug_level Rel --debug_level RelCheck" in
                  ()))
              else ());
             (let uu____617 = __do_unify env1 t1 t2 in
              FStar_Tactics_Monad.bind uu____617
                (fun r ->
                   (let uu____624 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "1346") in
                    if uu____624 then FStar_Options.pop () else ());
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
        let uu____648 = do_unify env1 t1 t2 in
        FStar_Tactics_Monad.bind uu____648
          (fun r ->
             if r
             then
               let uvs2 = FStar_Syntax_Free.uvars_uncached t1 in
               let uu____660 =
                 let uu____661 = FStar_Util.set_eq uvs1 uvs2 in
                 Prims.op_Negation uu____661 in
               (if uu____660
                then FStar_Tactics_Monad.ret false
                else FStar_Tactics_Monad.ret true)
             else FStar_Tactics_Monad.ret false)
let (set_solution :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____680 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
      match uu____680 with
      | FStar_Pervasives_Native.Some uu____685 ->
          let uu____686 =
            let uu____687 =
              FStar_Tactics_Printing.goal_to_string_verbose goal in
            FStar_Util.format1 "Goal %s is already solved" uu____687 in
          FStar_Tactics_Monad.fail uu____686
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
      let uu____703 = FStar_Tactics_Types.goal_env goal in
      let uu____704 = FStar_Tactics_Types.goal_witness goal in
      do_unify uu____703 solution uu____704
let (solve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let e = FStar_Tactics_Types.goal_env goal in
      FStar_Tactics_Monad.mlog
        (fun uu____723 ->
           let uu____724 =
             let uu____725 = FStar_Tactics_Types.goal_witness goal in
             FStar_Syntax_Print.term_to_string uu____725 in
           let uu____726 = FStar_Syntax_Print.term_to_string solution in
           FStar_Util.print2 "solve %s := %s\n" uu____724 uu____726)
        (fun uu____729 ->
           let uu____730 = trysolve goal solution in
           FStar_Tactics_Monad.bind uu____730
             (fun b ->
                if b
                then
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____738 -> FStar_Tactics_Monad.remove_solved_goals)
                else
                  (let uu____740 =
                     let uu____741 =
                       let uu____742 = FStar_Tactics_Types.goal_env goal in
                       tts uu____742 solution in
                     let uu____743 =
                       let uu____744 = FStar_Tactics_Types.goal_env goal in
                       let uu____745 = FStar_Tactics_Types.goal_witness goal in
                       tts uu____744 uu____745 in
                     let uu____746 =
                       let uu____747 = FStar_Tactics_Types.goal_env goal in
                       let uu____748 = FStar_Tactics_Types.goal_type goal in
                       tts uu____747 uu____748 in
                     FStar_Util.format3 "%s does not solve %s : %s" uu____741
                       uu____743 uu____746 in
                   FStar_Tactics_Monad.fail uu____740)))
let (solve' :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____763 = set_solution goal solution in
      FStar_Tactics_Monad.bind uu____763
        (fun uu____767 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
             (fun uu____769 -> FStar_Tactics_Monad.remove_solved_goals))
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____776 = FStar_Syntax_Util.un_squash t1 in
    match uu____776 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t' in
        let uu____787 =
          let uu____788 = FStar_Syntax_Subst.compress t'1 in
          uu____788.FStar_Syntax_Syntax.n in
        (match uu____787 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____792 -> false)
    | uu____793 -> false
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____803 = FStar_Syntax_Util.un_squash t in
    match uu____803 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____813 =
          let uu____814 = FStar_Syntax_Subst.compress t' in
          uu____814.FStar_Syntax_Syntax.n in
        (match uu____813 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____818 -> false)
    | uu____819 -> false
let (tadmit_t : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____833 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                (let uu____842 =
                   let uu____843 = FStar_Tactics_Types.goal_type g in
                   uu____843.FStar_Syntax_Syntax.pos in
                 let uu____846 =
                   let uu____851 =
                     let uu____852 =
                       FStar_Tactics_Printing.goal_to_string ""
                         FStar_Pervasives_Native.None ps g in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____852 in
                   (FStar_Errors.Warning_TacAdmit, uu____851) in
                 FStar_Errors.log_issue uu____842 uu____846);
                solve' g t)) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tadmit_t") uu____833
let (fresh : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____867 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let n = ps.FStar_Tactics_Types.freshness in
         let ps1 =
           let uu___200_877 = ps in
           {
             FStar_Tactics_Types.main_context =
               (uu___200_877.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (uu___200_877.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___200_877.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___200_877.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___200_877.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___200_877.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (uu___200_877.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___200_877.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___200_877.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___200_877.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___200_877.FStar_Tactics_Types.local_state)
           } in
         let uu____878 = FStar_Tactics_Monad.set ps1 in
         FStar_Tactics_Monad.bind uu____878
           (fun uu____883 ->
              let uu____884 = FStar_BigInt.of_int_fs n in
              FStar_Tactics_Monad.ret uu____884))
let (curms : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____891 ->
    let uu____894 =
      let uu____895 = FStar_Util.now_ms () in
      FStar_All.pipe_right uu____895 FStar_BigInt.of_int_fs in
    FStar_Tactics_Monad.ret uu____894
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
             (fun uu____938 ->
                let uu____939 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____939)
             (fun uu____942 ->
                let e1 =
                  let uu___209_944 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___209_944.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___209_944.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___209_944.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___209_944.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___209_944.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___209_944.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___209_944.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___209_944.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___209_944.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___209_944.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___209_944.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___209_944.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___209_944.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___209_944.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___209_944.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___209_944.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___209_944.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___209_944.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___209_944.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___209_944.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___209_944.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___209_944.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___209_944.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___209_944.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___209_944.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___209_944.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___209_944.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___209_944.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___209_944.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___209_944.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___209_944.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___209_944.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___209_944.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___209_944.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___209_944.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___209_944.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___209_944.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___209_944.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___209_944.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___209_944.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___209_944.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___209_944.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___209_944.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___209_944.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___209_944.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___209_944.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___213_955 ->
                     match () with
                     | () ->
                         let uu____964 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t in
                         FStar_Tactics_Monad.ret uu____964) ()
                with
                | FStar_Errors.Err (uu____991, msg) ->
                    let uu____993 = tts e1 t in
                    let uu____994 =
                      let uu____995 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____995
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____993 uu____994 msg
                | FStar_Errors.Error (uu____1002, msg, uu____1004) ->
                    let uu____1005 = tts e1 t in
                    let uu____1006 =
                      let uu____1007 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1007
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1005 uu____1006 msg))
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
             (fun uu____1056 ->
                let uu____1057 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____1057)
             (fun uu____1060 ->
                let e1 =
                  let uu___230_1062 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___230_1062.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___230_1062.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___230_1062.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___230_1062.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___230_1062.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___230_1062.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___230_1062.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___230_1062.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___230_1062.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___230_1062.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___230_1062.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___230_1062.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___230_1062.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___230_1062.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___230_1062.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___230_1062.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___230_1062.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___230_1062.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___230_1062.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___230_1062.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___230_1062.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___230_1062.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___230_1062.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___230_1062.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___230_1062.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___230_1062.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___230_1062.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___230_1062.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___230_1062.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___230_1062.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___230_1062.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___230_1062.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___230_1062.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___230_1062.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___230_1062.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___230_1062.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___230_1062.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___230_1062.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___230_1062.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___230_1062.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___230_1062.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___230_1062.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___230_1062.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___230_1062.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___230_1062.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___230_1062.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___234_1076 ->
                     match () with
                     | () ->
                         let uu____1085 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t in
                         (match uu____1085 with
                          | (t1, lc, g) ->
                              FStar_Tactics_Monad.ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu____1123, msg) ->
                    let uu____1125 = tts e1 t in
                    let uu____1126 =
                      let uu____1127 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1127
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1125 uu____1126 msg
                | FStar_Errors.Error (uu____1134, msg, uu____1136) ->
                    let uu____1137 = tts e1 t in
                    let uu____1138 =
                      let uu____1139 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1139
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1137 uu____1138 msg))
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
             (fun uu____1188 ->
                let uu____1189 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_lax(%s)\n" uu____1189)
             (fun uu____1193 ->
                let e1 =
                  let uu___255_1195 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___255_1195.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___255_1195.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___255_1195.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___255_1195.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___255_1195.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___255_1195.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___255_1195.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___255_1195.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___255_1195.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___255_1195.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___255_1195.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___255_1195.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___255_1195.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___255_1195.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___255_1195.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___255_1195.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___255_1195.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___255_1195.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___255_1195.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___255_1195.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___255_1195.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___255_1195.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___255_1195.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___255_1195.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___255_1195.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___255_1195.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___255_1195.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___255_1195.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___255_1195.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___255_1195.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___255_1195.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___255_1195.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___255_1195.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___255_1195.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___255_1195.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___255_1195.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___255_1195.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___255_1195.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___255_1195.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___255_1195.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___255_1195.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___255_1195.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___255_1195.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___255_1195.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___255_1195.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___255_1195.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                let e2 =
                  let uu___258_1197 = e1 in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___258_1197.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___258_1197.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___258_1197.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___258_1197.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___258_1197.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___258_1197.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___258_1197.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___258_1197.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___258_1197.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___258_1197.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___258_1197.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___258_1197.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___258_1197.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___258_1197.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___258_1197.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___258_1197.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___258_1197.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___258_1197.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___258_1197.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___258_1197.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___258_1197.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___258_1197.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___258_1197.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___258_1197.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___258_1197.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___258_1197.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___258_1197.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___258_1197.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___258_1197.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___258_1197.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___258_1197.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___258_1197.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___258_1197.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___258_1197.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___258_1197.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___258_1197.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___258_1197.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___258_1197.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___258_1197.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___258_1197.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___258_1197.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___258_1197.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___258_1197.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___258_1197.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___258_1197.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___258_1197.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___262_1208 ->
                     match () with
                     | () ->
                         let uu____1217 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t in
                         FStar_Tactics_Monad.ret uu____1217) ()
                with
                | FStar_Errors.Err (uu____1244, msg) ->
                    let uu____1246 = tts e2 t in
                    let uu____1247 =
                      let uu____1248 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1248
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1246 uu____1247 msg
                | FStar_Errors.Error (uu____1255, msg, uu____1257) ->
                    let uu____1258 = tts e2 t in
                    let uu____1259 =
                      let uu____1260 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1260
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1258 uu____1259 msg))
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
  fun uu____1287 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps -> FStar_Tactics_Monad.ret ps.FStar_Tactics_Types.guard_policy)
let (set_guard_policy :
  FStar_Tactics_Types.guard_policy -> unit FStar_Tactics_Monad.tac) =
  fun pol ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_Tactics_Monad.set
           (let uu___283_1305 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___283_1305.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___283_1305.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___283_1305.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___283_1305.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___283_1305.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___283_1305.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___283_1305.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___283_1305.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___283_1305.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___283_1305.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___283_1305.FStar_Tactics_Types.local_state)
            }))
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun pol ->
    fun t ->
      let uu____1329 = get_guard_policy () in
      FStar_Tactics_Monad.bind uu____1329
        (fun old_pol ->
           let uu____1335 = set_guard_policy pol in
           FStar_Tactics_Monad.bind uu____1335
             (fun uu____1339 ->
                FStar_Tactics_Monad.bind t
                  (fun r ->
                     let uu____1343 = set_guard_policy old_pol in
                     FStar_Tactics_Monad.bind uu____1343
                       (fun uu____1347 -> FStar_Tactics_Monad.ret r))))
let (getopts : FStar_Options.optionstate FStar_Tactics_Monad.tac) =
  let uu____1350 = trytac FStar_Tactics_Monad.cur_goal in
  FStar_Tactics_Monad.bind uu____1350
    (fun uu___0_1359 ->
       match uu___0_1359 with
       | FStar_Pervasives_Native.Some g ->
           FStar_Tactics_Monad.ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None ->
           let uu____1365 = FStar_Options.peek () in
           FStar_Tactics_Monad.ret uu____1365)
let (proc_guard :
  Prims.string ->
    env -> FStar_TypeChecker_Common.guard_t -> unit FStar_Tactics_Monad.tac)
  =
  fun reason ->
    fun e ->
      fun g ->
        FStar_Tactics_Monad.mlog
          (fun uu____1387 ->
             let uu____1388 = FStar_TypeChecker_Rel.guard_to_string e g in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____1388)
          (fun uu____1391 ->
             let uu____1392 =
               FStar_Tactics_Monad.add_implicits
                 g.FStar_TypeChecker_Common.implicits in
             FStar_Tactics_Monad.bind uu____1392
               (fun uu____1396 ->
                  FStar_Tactics_Monad.bind getopts
                    (fun opts ->
                       let uu____1400 =
                         let uu____1401 =
                           FStar_TypeChecker_Rel.simplify_guard e g in
                         uu____1401.FStar_TypeChecker_Common.guard_f in
                       match uu____1400 with
                       | FStar_TypeChecker_Common.Trivial ->
                           FStar_Tactics_Monad.ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____1405 = istrivial e f in
                           if uu____1405
                           then FStar_Tactics_Monad.ret ()
                           else
                             FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
                               (fun ps ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop ->
                                      ((let uu____1415 =
                                          let uu____1420 =
                                            let uu____1421 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____1421 in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____1420) in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____1415);
                                       FStar_Tactics_Monad.ret ())
                                  | FStar_Tactics_Types.Goal ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1424 ->
                                           let uu____1425 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____1425)
                                        (fun uu____1428 ->
                                           let uu____1429 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts "" in
                                           FStar_Tactics_Monad.bind
                                             uu____1429
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___312_1436 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___312_1436.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___312_1436.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___312_1436.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___312_1436.FStar_Tactics_Types.label)
                                                  } in
                                                FStar_Tactics_Monad.push_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.SMT ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1439 ->
                                           let uu____1440 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____1440)
                                        (fun uu____1443 ->
                                           let uu____1444 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts "" in
                                           FStar_Tactics_Monad.bind
                                             uu____1444
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___319_1451 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___319_1451.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___319_1451.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___319_1451.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___319_1451.FStar_Tactics_Types.label)
                                                  } in
                                                FStar_Tactics_Monad.push_smt_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.Force ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1454 ->
                                           let uu____1455 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____1455)
                                        (fun uu____1457 ->
                                           try
                                             (fun uu___326_1462 ->
                                                match () with
                                                | () ->
                                                    let uu____1465 =
                                                      let uu____1466 =
                                                        let uu____1467 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____1467 in
                                                      Prims.op_Negation
                                                        uu____1466 in
                                                    if uu____1465
                                                    then
                                                      FStar_Tactics_Monad.mlog
                                                        (fun uu____1472 ->
                                                           let uu____1473 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____1473)
                                                        (fun uu____1475 ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else
                                                      FStar_Tactics_Monad.ret
                                                        ()) ()
                                           with
                                           | uu___325_1478 ->
                                               FStar_Tactics_Monad.mlog
                                                 (fun uu____1483 ->
                                                    let uu____1484 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____1484)
                                                 (fun uu____1486 ->
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
      let uu____1501 =
        let uu____1504 = __tc_lax e t in
        FStar_Tactics_Monad.bind uu____1504
          (fun uu____1524 ->
             match uu____1524 with
             | (uu____1533, lc, uu____1535) ->
                 let uu____1536 =
                   let uu____1537 = FStar_TypeChecker_Common.lcomp_comp lc in
                   FStar_All.pipe_right uu____1537
                     FStar_Pervasives_Native.fst in
                 FStar_Tactics_Monad.ret uu____1536) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tcc") uu____1501
let (tc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Reflection_Data.typ FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu____1564 =
        let uu____1569 = tcc e t in
        FStar_Tactics_Monad.bind uu____1569
          (fun c -> FStar_Tactics_Monad.ret (FStar_Syntax_Util.comp_result c)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tc") uu____1564
let (trivial : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____1592 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____1598 =
           let uu____1599 = FStar_Tactics_Types.goal_env goal in
           let uu____1600 = FStar_Tactics_Types.goal_type goal in
           istrivial uu____1599 uu____1600 in
         if uu____1598
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____1604 =
              let uu____1605 = FStar_Tactics_Types.goal_env goal in
              let uu____1606 = FStar_Tactics_Types.goal_type goal in
              tts uu____1605 uu____1606 in
            fail1 "Not a trivial goal: %s" uu____1604))
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
             let uu____1655 =
               try
                 (fun uu___377_1678 ->
                    match () with
                    | () ->
                        let uu____1689 =
                          let uu____1698 = FStar_BigInt.to_int_fs n in
                          FStar_List.splitAt uu____1698
                            p.FStar_Tactics_Types.goals in
                        FStar_Tactics_Monad.ret uu____1689) ()
               with
               | uu___376_1708 ->
                   FStar_Tactics_Monad.fail "divide: not enough goals" in
             FStar_Tactics_Monad.bind uu____1655
               (fun uu____1744 ->
                  match uu____1744 with
                  | (lgs, rgs) ->
                      let lp =
                        let uu___359_1770 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___359_1770.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___359_1770.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___359_1770.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___359_1770.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___359_1770.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___359_1770.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___359_1770.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___359_1770.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___359_1770.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___359_1770.FStar_Tactics_Types.local_state)
                        } in
                      let uu____1771 = FStar_Tactics_Monad.set lp in
                      FStar_Tactics_Monad.bind uu____1771
                        (fun uu____1779 ->
                           FStar_Tactics_Monad.bind l
                             (fun a1 ->
                                FStar_Tactics_Monad.bind
                                  FStar_Tactics_Monad.get
                                  (fun lp' ->
                                     let rp =
                                       let uu___365_1795 = lp' in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___365_1795.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___365_1795.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___365_1795.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___365_1795.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___365_1795.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___365_1795.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___365_1795.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___365_1795.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___365_1795.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___365_1795.FStar_Tactics_Types.local_state)
                                       } in
                                     let uu____1796 =
                                       FStar_Tactics_Monad.set rp in
                                     FStar_Tactics_Monad.bind uu____1796
                                       (fun uu____1804 ->
                                          FStar_Tactics_Monad.bind r
                                            (fun b1 ->
                                               FStar_Tactics_Monad.bind
                                                 FStar_Tactics_Monad.get
                                                 (fun rp' ->
                                                    let p' =
                                                      let uu___371_1820 = rp' in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___371_1820.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___371_1820.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___371_1820.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___371_1820.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___371_1820.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___371_1820.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___371_1820.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___371_1820.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___371_1820.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___371_1820.FStar_Tactics_Types.local_state)
                                                      } in
                                                    let uu____1821 =
                                                      FStar_Tactics_Monad.set
                                                        p' in
                                                    FStar_Tactics_Monad.bind
                                                      uu____1821
                                                      (fun uu____1829 ->
                                                         FStar_Tactics_Monad.bind
                                                           FStar_Tactics_Monad.remove_solved_goals
                                                           (fun uu____1835 ->
                                                              FStar_Tactics_Monad.ret
                                                                (a1, b1)))))))))))
let focus : 'a . 'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac =
  fun f ->
    let uu____1856 = divide FStar_BigInt.one f FStar_Tactics_Monad.idtac in
    FStar_Tactics_Monad.bind uu____1856
      (fun uu____1869 ->
         match uu____1869 with | (a1, ()) -> FStar_Tactics_Monad.ret a1)
let rec map :
  'a . 'a FStar_Tactics_Monad.tac -> 'a Prims.list FStar_Tactics_Monad.tac =
  fun tau ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun p ->
         match p.FStar_Tactics_Types.goals with
         | [] -> FStar_Tactics_Monad.ret []
         | uu____1906::uu____1907 ->
             let uu____1910 =
               let uu____1919 = map tau in
               divide FStar_BigInt.one tau uu____1919 in
             FStar_Tactics_Monad.bind uu____1910
               (fun uu____1937 ->
                  match uu____1937 with
                  | (h, t) -> FStar_Tactics_Monad.ret (h :: t)))
let (seq :
  unit FStar_Tactics_Monad.tac ->
    unit FStar_Tactics_Monad.tac -> unit FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let uu____1978 =
        FStar_Tactics_Monad.bind t1
          (fun uu____1983 ->
             let uu____1984 = map t2 in
             FStar_Tactics_Monad.bind uu____1984
               (fun uu____1992 -> FStar_Tactics_Monad.ret ())) in
      focus uu____1978
let (intro : unit -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac) =
  fun uu____2001 ->
    let uu____2004 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____2013 =
             let uu____2020 =
               let uu____2021 = FStar_Tactics_Types.goal_env goal in
               let uu____2022 = FStar_Tactics_Types.goal_type goal in
               whnf uu____2021 uu____2022 in
             FStar_Syntax_Util.arrow_one uu____2020 in
           match uu____2013 with
           | FStar_Pervasives_Native.Some (b, c) ->
               let uu____2031 =
                 let uu____2032 = FStar_Syntax_Util.is_total_comp c in
                 Prims.op_Negation uu____2032 in
               if uu____2031
               then FStar_Tactics_Monad.fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2037 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.push_binders uu____2037 [b] in
                  let typ' = FStar_Syntax_Util.comp_result c in
                  let uu____2053 =
                    FStar_Tactics_Monad.new_uvar "intro" env' typ' in
                  FStar_Tactics_Monad.bind uu____2053
                    (fun uu____2069 ->
                       match uu____2069 with
                       | (body, ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)) in
                           let uu____2093 = set_solution goal sol in
                           FStar_Tactics_Monad.bind uu____2093
                             (fun uu____2099 ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label in
                                let uu____2101 =
                                  let uu____2104 = bnorm_goal g in
                                  FStar_Tactics_Monad.replace_cur uu____2104 in
                                FStar_Tactics_Monad.bind uu____2101
                                  (fun uu____2106 ->
                                     FStar_Tactics_Monad.ret b))))
           | FStar_Pervasives_Native.None ->
               let uu____2111 =
                 let uu____2112 = FStar_Tactics_Types.goal_env goal in
                 let uu____2113 = FStar_Tactics_Types.goal_type goal in
                 tts uu____2112 uu____2113 in
               fail1 "goal is not an arrow (%s)" uu____2111) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "intro") uu____2004
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder)
      FStar_Tactics_Monad.tac)
  =
  fun uu____2128 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2149 =
            let uu____2156 =
              let uu____2157 = FStar_Tactics_Types.goal_env goal in
              let uu____2158 = FStar_Tactics_Types.goal_type goal in
              whnf uu____2157 uu____2158 in
            FStar_Syntax_Util.arrow_one uu____2156 in
          match uu____2149 with
          | FStar_Pervasives_Native.Some (b, c) ->
              let uu____2171 =
                let uu____2172 = FStar_Syntax_Util.is_total_comp c in
                Prims.op_Negation uu____2172 in
              if uu____2171
              then FStar_Tactics_Monad.fail "Codomain is effectful"
              else
                (let bv =
                   let uu____2185 = FStar_Tactics_Types.goal_type goal in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____2185 in
                 let bs =
                   let uu____2195 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2195; b] in
                 let env' =
                   let uu____2221 = FStar_Tactics_Types.goal_env goal in
                   FStar_TypeChecker_Env.push_binders uu____2221 bs in
                 let uu____2222 =
                   FStar_Tactics_Monad.new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c) in
                 FStar_Tactics_Monad.bind uu____2222
                   (fun uu____2247 ->
                      match uu____2247 with
                      | (u, ctx_uvar_u) ->
                          let lb =
                            let uu____2261 =
                              FStar_Tactics_Types.goal_type goal in
                            let uu____2264 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____2261
                              FStar_Parser_Const.effect_Tot_lid uu____2264 []
                              FStar_Range.dummyRange in
                          let body = FStar_Syntax_Syntax.bv_to_name bv in
                          let uu____2282 =
                            FStar_Syntax_Subst.close_let_rec [lb] body in
                          (match uu____2282 with
                           | (lbs, body1) ->
                               let tm =
                                 let uu____2304 =
                                   let uu____2305 =
                                     FStar_Tactics_Types.goal_witness goal in
                                   uu____2305.FStar_Syntax_Syntax.pos in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1)) uu____2304 in
                               let uu____2318 = set_solution goal tm in
                               FStar_Tactics_Monad.bind uu____2318
                                 (fun uu____2327 ->
                                    let uu____2328 =
                                      let uu____2331 =
                                        bnorm_goal
                                          (let uu___442_2334 = goal in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___442_2334.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___442_2334.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___442_2334.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___442_2334.FStar_Tactics_Types.label)
                                           }) in
                                      FStar_Tactics_Monad.replace_cur
                                        uu____2331 in
                                    FStar_Tactics_Monad.bind uu____2328
                                      (fun uu____2341 ->
                                         let uu____2342 =
                                           let uu____2347 =
                                             FStar_Syntax_Syntax.mk_binder bv in
                                           (uu____2347, b) in
                                         FStar_Tactics_Monad.ret uu____2342)))))
          | FStar_Pervasives_Native.None ->
              let uu____2356 =
                let uu____2357 = FStar_Tactics_Types.goal_env goal in
                let uu____2358 = FStar_Tactics_Types.goal_type goal in
                tts uu____2357 uu____2358 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2356))
let (norm :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____2380 ->
              let uu____2381 =
                let uu____2382 = FStar_Tactics_Types.goal_witness goal in
                FStar_Syntax_Print.term_to_string uu____2382 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2381)
           (fun uu____2387 ->
              let steps =
                let uu____2391 = FStar_TypeChecker_Normalize.tr_norm_steps s in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____2391 in
              let t =
                let uu____2395 = FStar_Tactics_Types.goal_env goal in
                let uu____2396 = FStar_Tactics_Types.goal_type goal in
                normalize steps uu____2395 uu____2396 in
              let uu____2397 = FStar_Tactics_Types.goal_with_type goal t in
              FStar_Tactics_Monad.replace_cur uu____2397))
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun s ->
      fun t ->
        let uu____2421 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____2429 -> g.FStar_Tactics_Types.opts
                 | uu____2432 -> FStar_Options.peek () in
               FStar_Tactics_Monad.mlog
                 (fun uu____2437 ->
                    let uu____2438 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____2438)
                 (fun uu____2441 ->
                    let uu____2442 = __tc_lax e t in
                    FStar_Tactics_Monad.bind uu____2442
                      (fun uu____2463 ->
                         match uu____2463 with
                         | (t1, uu____2473, uu____2474) ->
                             let steps =
                               let uu____2478 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____2478 in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1 in
                             FStar_Tactics_Monad.mlog
                               (fun uu____2484 ->
                                  let uu____2485 =
                                    FStar_Syntax_Print.term_to_string t2 in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____2485)
                               (fun uu____2487 -> FStar_Tactics_Monad.ret t2)))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_term")
          uu____2421
let (refine_intro : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____2498 ->
    let uu____2501 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____2508 =
             let uu____2519 = FStar_Tactics_Types.goal_env g in
             let uu____2520 = FStar_Tactics_Types.goal_type g in
             FStar_TypeChecker_Rel.base_and_refinement uu____2519 uu____2520 in
           match uu____2508 with
           | (uu____2523, FStar_Pervasives_Native.None) ->
               FStar_Tactics_Monad.fail "not a refinement"
           | (t, FStar_Pervasives_Native.Some (bv, phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t in
               let uu____2548 =
                 let uu____2553 =
                   let uu____2558 =
                     let uu____2559 = FStar_Syntax_Syntax.mk_binder bv in
                     [uu____2559] in
                   FStar_Syntax_Subst.open_term uu____2558 phi in
                 match uu____2553 with
                 | (bvs, phi1) ->
                     let uu____2584 =
                       let uu____2585 = FStar_List.hd bvs in
                       FStar_Pervasives_Native.fst uu____2585 in
                     (uu____2584, phi1) in
               (match uu____2548 with
                | (bv1, phi1) ->
                    let uu____2604 =
                      let uu____2607 = FStar_Tactics_Types.goal_env g in
                      let uu____2608 =
                        let uu____2609 =
                          let uu____2612 =
                            let uu____2613 =
                              let uu____2620 =
                                FStar_Tactics_Types.goal_witness g in
                              (bv1, uu____2620) in
                            FStar_Syntax_Syntax.NT uu____2613 in
                          [uu____2612] in
                        FStar_Syntax_Subst.subst uu____2609 phi1 in
                      FStar_Tactics_Monad.mk_irrelevant_goal
                        "refine_intro refinement" uu____2607 uu____2608
                        g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label in
                    FStar_Tactics_Monad.bind uu____2604
                      (fun g2 ->
                         FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                           (fun uu____2628 ->
                              FStar_Tactics_Monad.add_goals [g1; g2])))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "refine_intro")
      uu____2501
let (__exact_now :
  Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun set_expected_typ ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let env1 =
             if set_expected_typ
             then
               let uu____2652 = FStar_Tactics_Types.goal_env goal in
               let uu____2653 = FStar_Tactics_Types.goal_type goal in
               FStar_TypeChecker_Env.set_expected_typ uu____2652 uu____2653
             else FStar_Tactics_Types.goal_env goal in
           let uu____2655 = __tc env1 t in
           FStar_Tactics_Monad.bind uu____2655
             (fun uu____2674 ->
                match uu____2674 with
                | (t1, typ, guard) ->
                    FStar_Tactics_Monad.mlog
                      (fun uu____2689 ->
                         let uu____2690 =
                           FStar_Syntax_Print.term_to_string typ in
                         let uu____2691 =
                           let uu____2692 = FStar_Tactics_Types.goal_env goal in
                           FStar_TypeChecker_Rel.guard_to_string uu____2692
                             guard in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____2690 uu____2691)
                      (fun uu____2695 ->
                         let uu____2696 =
                           let uu____2699 = FStar_Tactics_Types.goal_env goal in
                           proc_guard "__exact typing" uu____2699 guard in
                         FStar_Tactics_Monad.bind uu____2696
                           (fun uu____2701 ->
                              FStar_Tactics_Monad.mlog
                                (fun uu____2705 ->
                                   let uu____2706 =
                                     FStar_Syntax_Print.term_to_string typ in
                                   let uu____2707 =
                                     let uu____2708 =
                                       FStar_Tactics_Types.goal_type goal in
                                     FStar_Syntax_Print.term_to_string
                                       uu____2708 in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____2706 uu____2707)
                                (fun uu____2711 ->
                                   let uu____2712 =
                                     let uu____2715 =
                                       FStar_Tactics_Types.goal_env goal in
                                     let uu____2716 =
                                       FStar_Tactics_Types.goal_type goal in
                                     do_unify uu____2715 typ uu____2716 in
                                   FStar_Tactics_Monad.bind uu____2712
                                     (fun b ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____2722 =
                                             let uu____2727 =
                                               let uu____2732 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal in
                                               tts uu____2732 in
                                             let uu____2733 =
                                               FStar_Tactics_Types.goal_type
                                                 goal in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu____2727 typ uu____2733 in
                                           match uu____2722 with
                                           | (typ1, goalt) ->
                                               let uu____2738 =
                                                 let uu____2739 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 tts uu____2739 t1 in
                                               let uu____2740 =
                                                 let uu____2741 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 let uu____2742 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal in
                                                 tts uu____2741 uu____2742 in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu____2738 typ1 goalt
                                                 uu____2740)))))))
let (t_exact :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun try_refine ->
    fun set_expected_typ ->
      fun tm ->
        let uu____2762 =
          FStar_Tactics_Monad.mlog
            (fun uu____2767 ->
               let uu____2768 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2768)
            (fun uu____2771 ->
               let uu____2772 =
                 let uu____2779 = __exact_now set_expected_typ tm in
                 catch uu____2779 in
               FStar_Tactics_Monad.bind uu____2772
                 (fun uu___2_2788 ->
                    match uu___2_2788 with
                    | FStar_Util.Inr r -> FStar_Tactics_Monad.ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        FStar_Tactics_Monad.traise e
                    | FStar_Util.Inl e ->
                        FStar_Tactics_Monad.mlog
                          (fun uu____2799 ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____2802 ->
                             let uu____2803 =
                               let uu____2810 =
                                 let uu____2813 =
                                   norm [FStar_Syntax_Embeddings.Delta] in
                                 FStar_Tactics_Monad.bind uu____2813
                                   (fun uu____2818 ->
                                      let uu____2819 = refine_intro () in
                                      FStar_Tactics_Monad.bind uu____2819
                                        (fun uu____2823 ->
                                           __exact_now set_expected_typ tm)) in
                               catch uu____2810 in
                             FStar_Tactics_Monad.bind uu____2803
                               (fun uu___1_2830 ->
                                  match uu___1_2830 with
                                  | FStar_Util.Inr r ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____2839 ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____2841 ->
                                           FStar_Tactics_Monad.ret ())
                                  | FStar_Util.Inl uu____2842 ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____2844 ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____2846 ->
                                           FStar_Tactics_Monad.traise e))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "exact") uu____2762
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
            let uu____2939 = f e ty2 ty1 in
            FStar_Tactics_Monad.bind uu____2939
              (fun uu___3_2951 ->
                 if uu___3_2951
                 then FStar_Tactics_Monad.ret acc
                 else
                   (let uu____2970 = FStar_Syntax_Util.arrow_one ty1 in
                    match uu____2970 with
                    | FStar_Pervasives_Native.None ->
                        let uu____2991 = term_to_string e ty1 in
                        let uu____2992 = term_to_string e ty2 in
                        fail2 "Could not instantiate, %s to %s" uu____2991
                          uu____2992
                    | FStar_Pervasives_Native.Some (b, c) ->
                        let uu____3007 =
                          let uu____3008 = FStar_Syntax_Util.is_total_comp c in
                          Prims.op_Negation uu____3008 in
                        if uu____3007
                        then FStar_Tactics_Monad.fail "Codomain is effectful"
                        else
                          (let uu____3028 =
                             FStar_Tactics_Monad.new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           FStar_Tactics_Monad.bind uu____3028
                             (fun uu____3052 ->
                                match uu____3052 with
                                | (uvt, uv) ->
                                    FStar_Tactics_Monad.mlog
                                      (fun uu____3079 ->
                                         let uu____3080 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             uv in
                                         FStar_Util.print1
                                           "t_apply: generated uvar %s\n"
                                           uu____3080)
                                      (fun uu____3084 ->
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
        let uu____3166 =
          FStar_Tactics_Monad.mlog
            (fun uu____3171 ->
               let uu____3172 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____3172)
            (fun uu____3174 ->
               FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                 (fun goal ->
                    let e = FStar_Tactics_Types.goal_env goal in
                    FStar_Tactics_Monad.mlog
                      (fun uu____3183 ->
                         let uu____3184 =
                           FStar_Syntax_Print.term_to_string tm in
                         let uu____3185 =
                           FStar_Tactics_Printing.goal_to_string_verbose goal in
                         let uu____3186 =
                           FStar_TypeChecker_Env.print_gamma
                             e.FStar_TypeChecker_Env.gamma in
                         FStar_Util.print3
                           "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\n"
                           uu____3184 uu____3185 uu____3186)
                      (fun uu____3189 ->
                         let uu____3190 = __tc e tm in
                         FStar_Tactics_Monad.bind uu____3190
                           (fun uu____3211 ->
                              match uu____3211 with
                              | (tm1, typ, guard) ->
                                  let typ1 = bnorm e typ in
                                  let uu____3224 =
                                    let uu____3235 =
                                      FStar_Tactics_Types.goal_type goal in
                                    try_unify_by_application only_match e
                                      typ1 uu____3235 in
                                  FStar_Tactics_Monad.bind uu____3224
                                    (fun uvs ->
                                       FStar_Tactics_Monad.mlog
                                         (fun uu____3256 ->
                                            let uu____3257 =
                                              FStar_Common.string_of_list
                                                (fun uu____3268 ->
                                                   match uu____3268 with
                                                   | (t, uu____3276,
                                                      uu____3277) ->
                                                       FStar_Syntax_Print.term_to_string
                                                         t) uvs in
                                            FStar_Util.print1
                                              "t_apply: found args = %s\n"
                                              uu____3257)
                                         (fun uu____3284 ->
                                            let fix_qual q =
                                              match q with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.Meta
                                                  uu____3299) ->
                                                  FStar_Pervasives_Native.Some
                                                    (FStar_Syntax_Syntax.Implicit
                                                       false)
                                              | uu____3300 -> q in
                                            let w =
                                              FStar_List.fold_right
                                                (fun uu____3323 ->
                                                   fun w ->
                                                     match uu____3323 with
                                                     | (uvt, q, uu____3341)
                                                         ->
                                                         FStar_Syntax_Util.mk_app
                                                           w
                                                           [(uvt,
                                                              (fix_qual q))])
                                                uvs tm1 in
                                            let uvset =
                                              let uu____3373 =
                                                FStar_Syntax_Free.new_uv_set
                                                  () in
                                              FStar_List.fold_right
                                                (fun uu____3390 ->
                                                   fun s ->
                                                     match uu____3390 with
                                                     | (uu____3402,
                                                        uu____3403, uv) ->
                                                         let uu____3405 =
                                                           FStar_Syntax_Free.uvars
                                                             uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                         FStar_Util.set_union
                                                           s uu____3405) uvs
                                                uu____3373 in
                                            let free_in_some_goal uv =
                                              FStar_Util.set_mem uv uvset in
                                            let uu____3414 = solve' goal w in
                                            FStar_Tactics_Monad.bind
                                              uu____3414
                                              (fun uu____3419 ->
                                                 let uu____3420 =
                                                   FStar_Tactics_Monad.mapM
                                                     (fun uu____3437 ->
                                                        match uu____3437 with
                                                        | (uvt, q, uv) ->
                                                            let uu____3449 =
                                                              FStar_Syntax_Unionfind.find
                                                                uv.FStar_Syntax_Syntax.ctx_uvar_head in
                                                            (match uu____3449
                                                             with
                                                             | FStar_Pervasives_Native.Some
                                                                 uu____3454
                                                                 ->
                                                                 FStar_Tactics_Monad.ret
                                                                   ()
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 let uu____3455
                                                                   =
                                                                   uopt &&
                                                                    (free_in_some_goal
                                                                    uv) in
                                                                 if
                                                                   uu____3455
                                                                 then
                                                                   FStar_Tactics_Monad.ret
                                                                    ()
                                                                 else
                                                                   (let uu____3459
                                                                    =
                                                                    let uu____3462
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___605_3465
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___605_3465.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___605_3465.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___605_3465.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    [uu____3462] in
                                                                    FStar_Tactics_Monad.add_goals
                                                                    uu____3459)))
                                                     uvs in
                                                 FStar_Tactics_Monad.bind
                                                   uu____3420
                                                   (fun uu____3469 ->
                                                      proc_guard
                                                        "apply guard" e guard)))))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply") uu____3166
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c in
    let uu____3494 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid in
    if uu____3494
    then
      let uu____3501 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3516 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3569 -> failwith "apply_lemma: impossible: not a lemma" in
      match uu____3501 with
      | (pre, post) ->
          let post1 =
            let uu____3601 =
              let uu____3612 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
              [uu____3612] in
            FStar_Syntax_Util.mk_app post uu____3601 in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____3642 =
         (FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)
           ||
           (FStar_Syntax_Util.is_ghost_effect
              ct.FStar_Syntax_Syntax.effect_name) in
       if uu____3642
       then
         let uu____3649 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ in
         FStar_Util.map_opt uu____3649
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
            let uu____3726 = f x e in
            FStar_Tactics_Monad.bind uu____3726
              (fun e' -> fold_left f e' xs1)
let (apply_lemma : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun tm ->
    let uu____3740 =
      let uu____3743 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps ->
             FStar_Tactics_Monad.mlog
               (fun uu____3750 ->
                  let uu____3751 = FStar_Syntax_Print.term_to_string tm in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3751)
               (fun uu____3754 ->
                  let is_unit_t t =
                    let uu____3761 =
                      let uu____3762 = FStar_Syntax_Subst.compress t in
                      uu____3762.FStar_Syntax_Syntax.n in
                    match uu____3761 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____3766 -> false in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                    (fun goal ->
                       let env1 = FStar_Tactics_Types.goal_env goal in
                       let uu____3772 = __tc env1 tm in
                       FStar_Tactics_Monad.bind uu____3772
                         (fun uu____3795 ->
                            match uu____3795 with
                            | (tm1, t, guard) ->
                                let uu____3807 =
                                  FStar_Syntax_Util.arrow_formals_comp t in
                                (match uu____3807 with
                                 | (bs, comp) ->
                                     let uu____3816 = lemma_or_sq comp in
                                     (match uu____3816 with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Tactics_Monad.fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre, post) ->
                                          let uu____3835 =
                                            fold_left
                                              (fun uu____3897 ->
                                                 fun uu____3898 ->
                                                   match (uu____3897,
                                                           uu____3898)
                                                   with
                                                   | ((b, aq),
                                                      (uvs, imps, subst)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst
                                                           b.FStar_Syntax_Syntax.sort in
                                                       let uu____4049 =
                                                         is_unit_t b_t in
                                                       if uu____4049
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
                                                         (let uu____4169 =
                                                            FStar_Tactics_Monad.new_uvar
                                                              "apply_lemma"
                                                              env1 b_t in
                                                          FStar_Tactics_Monad.bind
                                                            uu____4169
                                                            (fun uu____4205
                                                               ->
                                                               match uu____4205
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
                                          FStar_Tactics_Monad.bind uu____3835
                                            (fun uu____4392 ->
                                               match uu____4392 with
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
                                                   let uu____4481 =
                                                     let uu____4484 =
                                                       FStar_Syntax_Util.mk_squash
                                                         post_u post1 in
                                                     let uu____4485 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal in
                                                     do_unify env1 uu____4484
                                                       uu____4485 in
                                                   FStar_Tactics_Monad.bind
                                                     uu____4481
                                                     (fun b ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____4494 =
                                                            let uu____4499 =
                                                              FStar_Syntax_Util.mk_squash
                                                                post_u post1 in
                                                            let uu____4500 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal in
                                                            FStar_TypeChecker_Err.print_discrepancy
                                                              (tts env1)
                                                              uu____4499
                                                              uu____4500 in
                                                          match uu____4494
                                                          with
                                                          | (post2, goalt) ->
                                                              let uu____4505
                                                                =
                                                                tts env1 tm1 in
                                                              fail3
                                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                uu____4505
                                                                post2 goalt
                                                        else
                                                          (let uu____4507 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit in
                                                           FStar_Tactics_Monad.bind
                                                             uu____4507
                                                             (fun uu____4515
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____4542
                                                                    =
                                                                    let uu____4545
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1 in
                                                                    FStar_Util.set_elements
                                                                    uu____4545 in
                                                                    FStar_List.map
                                                                    (fun x ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____4542 in
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
                                                                    let uu____4582
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g' in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____4582)
                                                                    goals in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____4598
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1 in
                                                                  match uu____4598
                                                                  with
                                                                  | (hd,
                                                                    uu____4616)
                                                                    ->
                                                                    (match 
                                                                    hd.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,
                                                                    uu____4642)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____4659
                                                                    -> false) in
                                                                let uu____4660
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    implicits2
                                                                    (
                                                                    FStar_Tactics_Monad.mapM
                                                                    (fun imp
                                                                    ->
                                                                    let uu____4701
                                                                    = imp in
                                                                    match uu____4701
                                                                    with
                                                                    | 
                                                                    (term,
                                                                    ctx_uvar)
                                                                    ->
                                                                    let uu____4712
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____4712
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu____4734)
                                                                    ->
                                                                    let uu____4759
                                                                    =
                                                                    let uu____4760
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd in
                                                                    uu____4760.FStar_Syntax_Syntax.n in
                                                                    (match uu____4759
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,
                                                                    uu____4768)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___726_4788
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___726_4788.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___726_4788.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___726_4788.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___726_4788.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    FStar_Tactics_Monad.ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____4791
                                                                    ->
                                                                    FStar_Tactics_Monad.mlog
                                                                    (fun
                                                                    uu____4797
                                                                    ->
                                                                    let uu____4798
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                                                                    let uu____4799
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____4798
                                                                    uu____4799)
                                                                    (fun
                                                                    uu____4803
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env1
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                                    let uu____4805
                                                                    =
                                                                    let uu____4808
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____4809
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar in
                                                                    let uu____4810
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____4809
                                                                    uu____4810
                                                                    else
                                                                    "apply_lemma solved arg" in
                                                                    proc_guard
                                                                    uu____4808
                                                                    env1
                                                                    g_typ in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____4805
                                                                    (fun
                                                                    uu____4815
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    [])))))) in
                                                                FStar_Tactics_Monad.bind
                                                                  uu____4660
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
                                                                    let uu____4877
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____4877
                                                                    then
                                                                    let uu____4880
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____4880
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g ->
                                                                    fun goals
                                                                    ->
                                                                    let uu____4894
                                                                    =
                                                                    let uu____4895
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g in
                                                                    checkone
                                                                    uu____4895
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____4894)
                                                                    sub_goals1 in
                                                                    let uu____4896
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    env1
                                                                    guard in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____4896
                                                                    (fun
                                                                    uu____4902
                                                                    ->
                                                                    let pre_u
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 pre1 in
                                                                    let uu____4904
                                                                    =
                                                                    let uu____4907
                                                                    =
                                                                    let uu____4908
                                                                    =
                                                                    let uu____4909
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre_u
                                                                    pre1 in
                                                                    istrivial
                                                                    env1
                                                                    uu____4909 in
                                                                    Prims.op_Negation
                                                                    uu____4908 in
                                                                    if
                                                                    uu____4907
                                                                    then
                                                                    FStar_Tactics_Monad.add_irrelevant_goal
                                                                    goal
                                                                    "apply_lemma precondition"
                                                                    env1 pre1
                                                                    else
                                                                    FStar_Tactics_Monad.ret
                                                                    () in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____4904
                                                                    (fun
                                                                    uu____4914
                                                                    ->
                                                                    FStar_Tactics_Monad.add_goals
                                                                    sub_goals2))))))))))))) in
      focus uu____3743 in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply_lemma")
      uu____3740
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____4936 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____4936 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,
         uu____4946::(e1, FStar_Pervasives_Native.None)::(e2,
                                                          FStar_Pervasives_Native.None)::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l, uu____5006::uu____5007::(e1, uu____5009)::(e2, uu____5011)::[]))
        when FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5088 ->
        let uu____5091 = FStar_Syntax_Util.unb2t typ in
        (match uu____5091 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____5105 = FStar_Syntax_Util.head_and_args t in
             (match uu____5105 with
              | (hd, args) ->
                  let uu____5154 =
                    let uu____5169 =
                      let uu____5170 = FStar_Syntax_Subst.compress hd in
                      uu____5170.FStar_Syntax_Syntax.n in
                    (uu____5169, args) in
                  (match uu____5154 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,
                      (uu____5190, FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____5191))::(e1,
                                                                    FStar_Pervasives_Native.None)::
                      (e2, FStar_Pervasives_Native.None)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____5258 -> FStar_Pervasives_Native.None)))
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____5294 = destruct_eq' typ in
    match uu____5294 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None ->
        let uu____5324 = FStar_Syntax_Util.un_squash typ in
        (match uu____5324 with
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
        let uu____5392 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____5392 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv', e') ->
            let uu____5427 = FStar_Syntax_Syntax.bv_eq bvar bv' in
            if uu____5427
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____5449 = aux e' in
               FStar_Util.map_opt uu____5449
                 (fun uu____5480 ->
                    match uu____5480 with
                    | (e'', bv, bvs) -> (e'', bv, (bv' :: bvs)))) in
      let uu____5506 = aux e in
      FStar_Util.map_opt uu____5506
        (fun uu____5537 ->
           match uu____5537 with
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
        let uu____5612 =
          let uu____5623 = FStar_Tactics_Types.goal_env g in
          split_env b1 uu____5623 in
        match uu____5612 with
        | FStar_Pervasives_Native.Some (e0, b11, bvs) ->
            let bs =
              FStar_List.map FStar_Syntax_Syntax.mk_binder (b11 :: bvs) in
            let t = FStar_Tactics_Types.goal_type g in
            let uu____5663 =
              let uu____5676 = FStar_Syntax_Subst.close_binders bs in
              let uu____5685 = FStar_Syntax_Subst.close bs t in
              (uu____5676, uu____5685) in
            (match uu____5663 with
             | (bs', t') ->
                 let bs'1 =
                   let uu____5729 = FStar_Syntax_Syntax.mk_binder b2 in
                   let uu____5736 = FStar_List.tail bs' in uu____5729 ::
                     uu____5736 in
                 let uu____5757 = FStar_Syntax_Subst.open_term bs'1 t' in
                 (match uu____5757 with
                  | (bs'', t'') ->
                      let b21 =
                        let uu____5773 = FStar_List.hd bs'' in
                        FStar_Pervasives_Native.fst uu____5773 in
                      let new_env =
                        let uu____5789 =
                          FStar_List.map FStar_Pervasives_Native.fst bs'' in
                        push_bvs e0 uu____5789 in
                      let uu____5800 =
                        FStar_Tactics_Monad.new_uvar "subst_goal" new_env t'' in
                      FStar_Tactics_Monad.bind uu____5800
                        (fun uu____5823 ->
                           match uu____5823 with
                           | (uvt, uv) ->
                               let goal' =
                                 FStar_Tactics_Types.mk_goal new_env uv
                                   g.FStar_Tactics_Types.opts
                                   g.FStar_Tactics_Types.is_guard
                                   g.FStar_Tactics_Types.label in
                               let sol =
                                 let uu____5842 =
                                   FStar_Syntax_Util.abs bs'' uvt
                                     FStar_Pervasives_Native.None in
                                 let uu____5845 =
                                   FStar_List.map
                                     (fun uu____5866 ->
                                        match uu____5866 with
                                        | (bv, q) ->
                                            let uu____5879 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                bv in
                                            FStar_Syntax_Syntax.as_arg
                                              uu____5879) bs in
                                 FStar_Syntax_Util.mk_app uu____5842
                                   uu____5845 in
                               let uu____5880 = set_solution g sol in
                               FStar_Tactics_Monad.bind uu____5880
                                 (fun uu____5890 ->
                                    FStar_Tactics_Monad.ret
                                      (FStar_Pervasives_Native.Some
                                         (b21, goal'))))))
        | FStar_Pervasives_Native.None ->
            FStar_Tactics_Monad.ret FStar_Pervasives_Native.None
let (rewrite : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun h ->
    let uu____5928 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____5936 = h in
           match uu____5936 with
           | (bv, uu____5940) ->
               FStar_Tactics_Monad.mlog
                 (fun uu____5948 ->
                    let uu____5949 = FStar_Syntax_Print.bv_to_string bv in
                    let uu____5950 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5949
                      uu____5950)
                 (fun uu____5953 ->
                    let uu____5954 =
                      let uu____5965 = FStar_Tactics_Types.goal_env goal in
                      split_env bv uu____5965 in
                    match uu____5954 with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.fail
                          "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                        let uu____5991 =
                          let uu____5998 =
                            whnf e0 bv1.FStar_Syntax_Syntax.sort in
                          destruct_eq uu____5998 in
                        (match uu____5991 with
                         | FStar_Pervasives_Native.Some (x, e) ->
                             let uu____6007 =
                               let uu____6008 = FStar_Syntax_Subst.compress x in
                               uu____6008.FStar_Syntax_Syntax.n in
                             (match uu____6007 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                  let t = FStar_Tactics_Types.goal_type goal in
                                  let bs =
                                    FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder bvs in
                                  let uu____6035 =
                                    let uu____6040 =
                                      FStar_Syntax_Subst.close_binders bs in
                                    let uu____6041 =
                                      FStar_Syntax_Subst.close bs t in
                                    (uu____6040, uu____6041) in
                                  (match uu____6035 with
                                   | (bs', t') ->
                                       let uu____6046 =
                                         let uu____6051 =
                                           FStar_Syntax_Subst.subst_binders s
                                             bs' in
                                         let uu____6052 =
                                           FStar_Syntax_Subst.subst s t in
                                         (uu____6051, uu____6052) in
                                       (match uu____6046 with
                                        | (bs'1, t'1) ->
                                            let uu____6057 =
                                              FStar_Syntax_Subst.open_term
                                                bs'1 t'1 in
                                            (match uu____6057 with
                                             | (bs'', t'') ->
                                                 let new_env =
                                                   let uu____6067 =
                                                     let uu____6070 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         bs'' in
                                                     bv1 :: uu____6070 in
                                                   push_bvs e0 uu____6067 in
                                                 let uu____6081 =
                                                   FStar_Tactics_Monad.new_uvar
                                                     "rewrite" new_env t'' in
                                                 FStar_Tactics_Monad.bind
                                                   uu____6081
                                                   (fun uu____6098 ->
                                                      match uu____6098 with
                                                      | (uvt, uv) ->
                                                          let goal' =
                                                            FStar_Tactics_Types.mk_goal
                                                              new_env uv
                                                              goal.FStar_Tactics_Types.opts
                                                              goal.FStar_Tactics_Types.is_guard
                                                              goal.FStar_Tactics_Types.label in
                                                          let sol =
                                                            let uu____6111 =
                                                              FStar_Syntax_Util.abs
                                                                bs'' uvt
                                                                FStar_Pervasives_Native.None in
                                                            let uu____6114 =
                                                              FStar_List.map
                                                                (fun
                                                                   uu____6135
                                                                   ->
                                                                   match uu____6135
                                                                   with
                                                                   | 
                                                                   (bv2,
                                                                    uu____6143)
                                                                    ->
                                                                    let uu____6148
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv2 in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____6148)
                                                                bs in
                                                            FStar_Syntax_Util.mk_app
                                                              uu____6111
                                                              uu____6114 in
                                                          let uu____6149 =
                                                            set_solution goal
                                                              sol in
                                                          FStar_Tactics_Monad.bind
                                                            uu____6149
                                                            (fun uu____6153
                                                               ->
                                                               FStar_Tactics_Monad.replace_cur
                                                                 goal')))))
                              | uu____6154 ->
                                  FStar_Tactics_Monad.fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6155 ->
                             FStar_Tactics_Monad.fail
                               "Not an equality hypothesis"))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rewrite") uu____5928
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac)
  =
  fun b ->
    fun s ->
      let uu____6180 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____6202 = b in
             match uu____6202 with
             | (bv, q) ->
                 let bv' =
                   let uu____6218 =
                     let uu___904_6219 = bv in
                     let uu____6220 =
                       let uu____6221 =
                         let uu____6226 =
                           FStar_Ident.range_of_id
                             bv.FStar_Syntax_Syntax.ppname in
                         (s, uu____6226) in
                       FStar_Ident.mk_ident uu____6221 in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6220;
                       FStar_Syntax_Syntax.index =
                         (uu___904_6219.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___904_6219.FStar_Syntax_Syntax.sort)
                     } in
                   FStar_Syntax_Syntax.freshen_bv uu____6218 in
                 let uu____6227 = subst_goal bv bv' goal in
                 FStar_Tactics_Monad.bind uu____6227
                   (fun uu___4_6249 ->
                      match uu___4_6249 with
                      | FStar_Pervasives_Native.None ->
                          FStar_Tactics_Monad.fail
                            "binder not found in environment"
                      | FStar_Pervasives_Native.Some (bv'1, goal1) ->
                          let uu____6280 =
                            FStar_Tactics_Monad.replace_cur goal1 in
                          FStar_Tactics_Monad.bind uu____6280
                            (fun uu____6290 ->
                               FStar_Tactics_Monad.ret (bv'1, q)))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rename_to")
        uu____6180
let (binder_retype :
  FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let uu____6324 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____6333 = b in
           match uu____6333 with
           | (bv, uu____6337) ->
               let uu____6342 =
                 let uu____6353 = FStar_Tactics_Types.goal_env goal in
                 split_env bv uu____6353 in
               (match uu____6342 with
                | FStar_Pervasives_Native.None ->
                    FStar_Tactics_Monad.fail
                      "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                    let uu____6379 = FStar_Syntax_Util.type_u () in
                    (match uu____6379 with
                     | (ty, u) ->
                         let uu____6388 =
                           FStar_Tactics_Monad.new_uvar "binder_retype" e0 ty in
                         FStar_Tactics_Monad.bind uu____6388
                           (fun uu____6406 ->
                              match uu____6406 with
                              | (t', u_t') ->
                                  let bv'' =
                                    let uu___931_6416 = bv1 in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___931_6416.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___931_6416.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    } in
                                  let s =
                                    let uu____6420 =
                                      let uu____6421 =
                                        let uu____6428 =
                                          FStar_Syntax_Syntax.bv_to_name bv'' in
                                        (bv1, uu____6428) in
                                      FStar_Syntax_Syntax.NT uu____6421 in
                                    [uu____6420] in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1 ->
                                         let uu___936_6440 = b1 in
                                         let uu____6441 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___936_6440.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___936_6440.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6441
                                         }) bvs in
                                  let env' = push_bvs e0 (bv'' :: bvs1) in
                                  FStar_Tactics_Monad.bind
                                    FStar_Tactics_Monad.dismiss
                                    (fun uu____6448 ->
                                       let new_goal =
                                         let uu____6450 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env' in
                                         let uu____6451 =
                                           let uu____6452 =
                                             FStar_Tactics_Types.goal_type
                                               goal in
                                           FStar_Syntax_Subst.subst s
                                             uu____6452 in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6450 uu____6451 in
                                       let uu____6453 =
                                         FStar_Tactics_Monad.add_goals
                                           [new_goal] in
                                       FStar_Tactics_Monad.bind uu____6453
                                         (fun uu____6458 ->
                                            let uu____6459 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t' in
                                            FStar_Tactics_Monad.add_irrelevant_goal
                                              goal "binder_retype equation"
                                              e0 uu____6459)))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "binder_retype")
      uu____6324
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    fun b ->
      let uu____6482 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____6491 = b in
             match uu____6491 with
             | (bv, uu____6495) ->
                 let uu____6500 =
                   let uu____6511 = FStar_Tactics_Types.goal_env goal in
                   split_env bv uu____6511 in
                 (match uu____6500 with
                  | FStar_Pervasives_Native.None ->
                      FStar_Tactics_Monad.fail
                        "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                      let steps =
                        let uu____6540 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6540 in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort in
                      let bv' =
                        let uu___957_6545 = bv1 in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___957_6545.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___957_6545.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        } in
                      let env' = push_bvs e0 (bv' :: bvs) in
                      let uu____6547 =
                        FStar_Tactics_Types.goal_with_env goal env' in
                      FStar_Tactics_Monad.replace_cur uu____6547)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_binder_type")
        uu____6482
let (revert : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____6558 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____6564 =
           let uu____6571 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____6571 in
         match uu____6564 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x, env') ->
             let typ' =
               let uu____6587 =
                 let uu____6590 = FStar_Tactics_Types.goal_type goal in
                 FStar_Syntax_Syntax.mk_Total uu____6590 in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6587 in
             let uu____6605 = FStar_Tactics_Monad.new_uvar "revert" env' typ' in
             FStar_Tactics_Monad.bind uu____6605
               (fun uu____6620 ->
                  match uu____6620 with
                  | (r, u_r) ->
                      let uu____6629 =
                        let uu____6632 =
                          let uu____6633 =
                            let uu____6634 =
                              let uu____6643 =
                                FStar_Syntax_Syntax.bv_to_name x in
                              FStar_Syntax_Syntax.as_arg uu____6643 in
                            [uu____6634] in
                          let uu____6660 =
                            let uu____6661 =
                              FStar_Tactics_Types.goal_type goal in
                            uu____6661.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.mk_Tm_app r uu____6633
                            uu____6660 in
                        set_solution goal uu____6632 in
                      FStar_Tactics_Monad.bind uu____6629
                        (fun uu____6666 ->
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
      let uu____6678 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____6678
let (clear : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let bv = FStar_Pervasives_Native.fst b in
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____6698 ->
              let uu____6699 = FStar_Syntax_Print.binder_to_string b in
              let uu____6700 =
                let uu____6701 =
                  let uu____6702 =
                    let uu____6711 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.all_binders uu____6711 in
                  FStar_All.pipe_right uu____6702 FStar_List.length in
                FStar_All.pipe_right uu____6701 FStar_Util.string_of_int in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6699 uu____6700)
           (fun uu____6728 ->
              let uu____6729 =
                let uu____6740 = FStar_Tactics_Types.goal_env goal in
                split_env bv uu____6740 in
              match uu____6729 with
              | FStar_Pervasives_Native.None ->
                  FStar_Tactics_Monad.fail
                    "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e', bv1, bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> FStar_Tactics_Monad.ret ()
                    | bv'::bvs2 ->
                        let uu____6784 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort in
                        if uu____6784
                        then
                          let uu____6787 =
                            let uu____6788 =
                              FStar_Syntax_Print.bv_to_string bv' in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6788 in
                          FStar_Tactics_Monad.fail uu____6787
                        else check bvs2 in
                  let uu____6790 =
                    let uu____6791 = FStar_Tactics_Types.goal_type goal in
                    free_in bv1 uu____6791 in
                  if uu____6790
                  then
                    FStar_Tactics_Monad.fail
                      "Cannot clear; binder present in goal"
                  else
                    (let uu____6795 = check bvs in
                     FStar_Tactics_Monad.bind uu____6795
                       (fun uu____6801 ->
                          let env' = push_bvs e' bvs in
                          let uu____6803 =
                            let uu____6810 =
                              FStar_Tactics_Types.goal_type goal in
                            FStar_Tactics_Monad.new_uvar "clear.witness" env'
                              uu____6810 in
                          FStar_Tactics_Monad.bind uu____6803
                            (fun uu____6819 ->
                               match uu____6819 with
                               | (ut, uvar_ut) ->
                                   let uu____6828 = set_solution goal ut in
                                   FStar_Tactics_Monad.bind uu____6828
                                     (fun uu____6833 ->
                                        let uu____6834 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label in
                                        FStar_Tactics_Monad.replace_cur
                                          uu____6834))))))
let (clear_top : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____6841 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____6847 =
           let uu____6854 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____6854 in
         match uu____6847 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x, uu____6862) ->
             let uu____6867 = FStar_Syntax_Syntax.mk_binder x in
             clear uu____6867)
let (prune : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____6884 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6884 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (addns : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____6902 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6902 in
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
           let uu____6921 =
             let uu____6924 = FStar_Tactics_Types.goal_env g in
             do_unify uu____6924 l r in
           FStar_Tactics_Monad.bind uu____6921
             (fun b ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____6931 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____6931 l in
                   let r1 =
                     let uu____6933 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____6933 r in
                   let uu____6934 =
                     let uu____6937 = FStar_Tactics_Types.goal_env g in
                     do_unify uu____6937 l1 r1 in
                   FStar_Tactics_Monad.bind uu____6934
                     (fun b1 ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____6943 =
                             let uu____6948 =
                               let uu____6953 =
                                 FStar_Tactics_Types.goal_env g in
                               tts uu____6953 in
                             FStar_TypeChecker_Err.print_discrepancy
                               uu____6948 l1 r1 in
                           match uu____6943 with
                           | (ls, rs) ->
                               fail2 "not a trivial equality ((%s) vs (%s))"
                                 ls rs)))))
let (trefl : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____6964 ->
    let uu____6967 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____6975 =
             let uu____6982 =
               let uu____6983 = FStar_Tactics_Types.goal_env g in
               let uu____6984 = FStar_Tactics_Types.goal_type g in
               whnf uu____6983 uu____6984 in
             destruct_eq uu____6982 in
           match uu____6975 with
           | FStar_Pervasives_Native.Some (l, r) -> _trefl l r
           | FStar_Pervasives_Native.None ->
               let uu____6997 =
                 let uu____6998 = FStar_Tactics_Types.goal_env g in
                 let uu____6999 = FStar_Tactics_Types.goal_type g in
                 tts uu____6998 uu____6999 in
               fail1 "not an equality (%s)" uu____6997) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "trefl") uu____6967
let (dup : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7010 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let env1 = FStar_Tactics_Types.goal_env g in
         let uu____7018 =
           let uu____7025 = FStar_Tactics_Types.goal_type g in
           FStar_Tactics_Monad.new_uvar "dup" env1 uu____7025 in
         FStar_Tactics_Monad.bind uu____7018
           (fun uu____7034 ->
              match uu____7034 with
              | (u, u_uvar) ->
                  let g' =
                    let uu___1043_7044 = g in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1043_7044.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1043_7044.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1043_7044.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1043_7044.FStar_Tactics_Types.label)
                    } in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____7048 ->
                       let t_eq =
                         let uu____7050 =
                           let uu____7051 = FStar_Tactics_Types.goal_type g in
                           env1.FStar_TypeChecker_Env.universe_of env1
                             uu____7051 in
                         let uu____7052 = FStar_Tactics_Types.goal_type g in
                         let uu____7053 = FStar_Tactics_Types.goal_witness g in
                         FStar_Syntax_Util.mk_eq2 uu____7050 uu____7052 u
                           uu____7053 in
                       let uu____7054 =
                         FStar_Tactics_Monad.add_irrelevant_goal g
                           "dup equation" env1 t_eq in
                       FStar_Tactics_Monad.bind uu____7054
                         (fun uu____7059 ->
                            let uu____7060 =
                              FStar_Tactics_Monad.add_goals [g'] in
                            FStar_Tactics_Monad.bind uu____7060
                              (fun uu____7064 -> FStar_Tactics_Monad.ret ())))))
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
              let uu____7187 = f x y in
              if uu____7187 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____7207 -> (acc, l11, l21) in
        let uu____7222 = aux [] l1 l2 in
        match uu____7222 with | (pr, t1, t2) -> ((FStar_List.rev pr), t1, t2)
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
      let uu____7327 = FStar_Tactics_Types.get_phi g1 in
      match uu____7327 with
      | FStar_Pervasives_Native.None ->
          FStar_Tactics_Monad.fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____7333 = FStar_Tactics_Types.get_phi g2 in
          (match uu____7333 with
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let uu____7345 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2) in
               (match uu____7345 with
                | (gamma, r1, r2) ->
                    let t1 =
                      let uu____7376 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1) in
                      close_forall_no_univs uu____7376 phi1 in
                    let t2 =
                      let uu____7386 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2) in
                      close_forall_no_univs uu____7386 phi2 in
                    let uu____7395 =
                      set_solution g1 FStar_Syntax_Util.exp_unit in
                    FStar_Tactics_Monad.bind uu____7395
                      (fun uu____7400 ->
                         let uu____7401 =
                           set_solution g2 FStar_Syntax_Util.exp_unit in
                         FStar_Tactics_Monad.bind uu____7401
                           (fun uu____7408 ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2 in
                              let nenv =
                                let uu___1095_7413 =
                                  FStar_Tactics_Types.goal_env g1 in
                                let uu____7414 =
                                  FStar_Util.smap_create (Prims.of_int (100)) in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1095_7413.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1095_7413.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1095_7413.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1095_7413.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____7414;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1095_7413.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1095_7413.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1095_7413.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1095_7413.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1095_7413.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1095_7413.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1095_7413.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1095_7413.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1095_7413.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1095_7413.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1095_7413.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1095_7413.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1095_7413.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1095_7413.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1095_7413.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1095_7413.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1095_7413.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1095_7413.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1095_7413.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1095_7413.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1095_7413.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1095_7413.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1095_7413.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1095_7413.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1095_7413.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1095_7413.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1095_7413.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1095_7413.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1095_7413.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1095_7413.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1095_7413.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1095_7413.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1095_7413.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1095_7413.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1095_7413.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1095_7413.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1095_7413.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1095_7413.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1095_7413.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1095_7413.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___1095_7413.FStar_TypeChecker_Env.enable_defer_to_tac)
                                } in
                              let uu____7417 =
                                FStar_Tactics_Monad.mk_irrelevant_goal
                                  "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label in
                              FStar_Tactics_Monad.bind uu____7417
                                (fun goal ->
                                   FStar_Tactics_Monad.mlog
                                     (fun uu____7426 ->
                                        let uu____7427 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g1 in
                                        let uu____7428 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g2 in
                                        let uu____7429 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            goal in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____7427 uu____7428 uu____7429)
                                     (fun uu____7431 ->
                                        FStar_Tactics_Monad.ret goal))))))
let (join : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7438 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____7454 =
               FStar_Tactics_Monad.set
                 (let uu___1110_7459 = ps in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1110_7459.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1110_7459.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1110_7459.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1110_7459.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1110_7459.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1110_7459.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1110_7459.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1110_7459.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1110_7459.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1110_7459.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1110_7459.FStar_Tactics_Types.local_state)
                  }) in
             FStar_Tactics_Monad.bind uu____7454
               (fun uu____7462 ->
                  let uu____7463 = join_goals g1 g2 in
                  FStar_Tactics_Monad.bind uu____7463
                    (fun g12 -> FStar_Tactics_Monad.add_goals [g12]))
         | uu____7468 -> FStar_Tactics_Monad.fail "join: less than 2 goals")
let (set_options : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    let uu____7480 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           FStar_Options.push ();
           (let uu____7493 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
            FStar_Options.set uu____7493);
           (let res = FStar_Options.set_options s in
            let opts' = FStar_Options.peek () in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success ->
                 let g' =
                   let uu___1121_7500 = g in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1121_7500.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1121_7500.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1121_7500.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1121_7500.FStar_Tactics_Types.label)
                   } in
                 FStar_Tactics_Monad.replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "set_options")
      uu____7480
let (top_env : unit -> env FStar_Tactics_Monad.tac) =
  fun uu____7512 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_All.pipe_left FStar_Tactics_Monad.ret
           ps.FStar_Tactics_Types.main_context)
let (lax_on : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____7525 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let uu____7531 =
           (FStar_Options.lax ()) ||
             (let uu____7533 = FStar_Tactics_Types.goal_env g in
              uu____7533.FStar_TypeChecker_Env.lax) in
         FStar_Tactics_Monad.ret uu____7531)
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun tm ->
      let uu____7548 =
        FStar_Tactics_Monad.mlog
          (fun uu____7553 ->
             let uu____7554 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "unquote: tm = %s\n" uu____7554)
          (fun uu____7556 ->
             FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
               (fun goal ->
                  let env1 =
                    let uu____7562 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.set_expected_typ uu____7562 ty in
                  let uu____7563 = __tc_ghost env1 tm in
                  FStar_Tactics_Monad.bind uu____7563
                    (fun uu____7582 ->
                       match uu____7582 with
                       | (tm1, typ, guard) ->
                           FStar_Tactics_Monad.mlog
                             (fun uu____7596 ->
                                let uu____7597 =
                                  FStar_Syntax_Print.term_to_string tm1 in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____7597)
                             (fun uu____7599 ->
                                FStar_Tactics_Monad.mlog
                                  (fun uu____7602 ->
                                     let uu____7603 =
                                       FStar_Syntax_Print.term_to_string typ in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____7603)
                                  (fun uu____7606 ->
                                     let uu____7607 =
                                       proc_guard "unquote" env1 guard in
                                     FStar_Tactics_Monad.bind uu____7607
                                       (fun uu____7611 ->
                                          FStar_Tactics_Monad.ret tm1)))))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unquote") uu____7548
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun ty ->
      let uu____7634 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> FStar_Tactics_Monad.ret ty1
        | FStar_Pervasives_Native.None ->
            let uu____7640 =
              let uu____7647 =
                let uu____7648 = FStar_Syntax_Util.type_u () in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7648 in
              FStar_Tactics_Monad.new_uvar "uvar_env.2" env1 uu____7647 in
            FStar_Tactics_Monad.bind uu____7640
              (fun uu____7664 ->
                 match uu____7664 with
                 | (typ, uvar_typ) -> FStar_Tactics_Monad.ret typ) in
      FStar_Tactics_Monad.bind uu____7634
        (fun typ ->
           let uu____7676 = FStar_Tactics_Monad.new_uvar "uvar_env" env1 typ in
           FStar_Tactics_Monad.bind uu____7676
             (fun uu____7690 ->
                match uu____7690 with
                | (t, uvar_t) -> FStar_Tactics_Monad.ret t))
let (unshelve : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____7708 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           let env1 = ps.FStar_Tactics_Types.main_context in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____7727 -> g.FStar_Tactics_Types.opts
             | uu____7730 -> FStar_Options.peek () in
           let uu____7733 = FStar_Syntax_Util.head_and_args t in
           match uu____7733 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar, uu____7753);
                FStar_Syntax_Syntax.pos = uu____7754;
                FStar_Syntax_Syntax.vars = uu____7755;_},
              uu____7756) ->
               let env2 =
                 let uu___1175_7798 = env1 in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1175_7798.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1175_7798.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1175_7798.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1175_7798.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1175_7798.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1175_7798.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1175_7798.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1175_7798.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1175_7798.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1175_7798.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1175_7798.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1175_7798.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1175_7798.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1175_7798.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1175_7798.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1175_7798.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___1175_7798.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1175_7798.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1175_7798.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1175_7798.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1175_7798.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1175_7798.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1175_7798.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1175_7798.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1175_7798.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1175_7798.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1175_7798.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1175_7798.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1175_7798.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1175_7798.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1175_7798.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1175_7798.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1175_7798.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1175_7798.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1175_7798.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___1175_7798.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1175_7798.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1175_7798.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1175_7798.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1175_7798.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1175_7798.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1175_7798.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1175_7798.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1175_7798.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1175_7798.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (uu___1175_7798.FStar_TypeChecker_Env.enable_defer_to_tac)
                 } in
               let g =
                 FStar_Tactics_Types.mk_goal env2 ctx_uvar opts false "" in
               let uu____7800 = let uu____7803 = bnorm_goal g in [uu____7803] in
               FStar_Tactics_Monad.add_goals uu____7800
           | uu____7804 -> FStar_Tactics_Monad.fail "not a uvar") in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unshelve") uu____7708
let (tac_and :
  Prims.bool FStar_Tactics_Monad.tac ->
    Prims.bool FStar_Tactics_Monad.tac -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let comp =
        FStar_Tactics_Monad.bind t1
          (fun b ->
             let uu____7853 = if b then t2 else FStar_Tactics_Monad.ret false in
             FStar_Tactics_Monad.bind uu____7853
               (fun b' ->
                  if b'
                  then FStar_Tactics_Monad.ret b'
                  else FStar_Tactics_Monad.fail "")) in
      let uu____7864 = trytac comp in
      FStar_Tactics_Monad.bind uu____7864
        (fun uu___5_7872 ->
           match uu___5_7872 with
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
        let uu____7898 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu____7904 = __tc e t1 in
               FStar_Tactics_Monad.bind uu____7904
                 (fun uu____7924 ->
                    match uu____7924 with
                    | (t11, ty1, g1) ->
                        let uu____7936 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu____7936
                          (fun uu____7956 ->
                             match uu____7956 with
                             | (t21, ty2, g2) ->
                                 let uu____7968 =
                                   proc_guard "unify_env g1" e g1 in
                                 FStar_Tactics_Monad.bind uu____7968
                                   (fun uu____7973 ->
                                      let uu____7974 =
                                        proc_guard "unify_env g2" e g2 in
                                      FStar_Tactics_Monad.bind uu____7974
                                        (fun uu____7980 ->
                                           let uu____7981 =
                                             do_unify e ty1 ty2 in
                                           let uu____7984 =
                                             do_unify e t11 t21 in
                                           tac_and uu____7981 uu____7984))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unify_env")
          uu____7898
let (launch_process :
  Prims.string ->
    Prims.string Prims.list ->
      Prims.string -> Prims.string FStar_Tactics_Monad.tac)
  =
  fun prog ->
    fun args ->
      fun input ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____8017 ->
             let uu____8018 = FStar_Options.unsafe_tactic_exec () in
             if uu____8018
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
        (fun uu____8039 ->
           let uu____8040 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t in
           FStar_Tactics_Monad.ret uu____8040)
let (change : FStar_Reflection_Data.typ -> unit FStar_Tactics_Monad.tac) =
  fun ty ->
    let uu____8050 =
      FStar_Tactics_Monad.mlog
        (fun uu____8055 ->
           let uu____8056 = FStar_Syntax_Print.term_to_string ty in
           FStar_Util.print1 "change: ty = %s\n" uu____8056)
        (fun uu____8058 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                let uu____8062 =
                  let uu____8071 = FStar_Tactics_Types.goal_env g in
                  __tc uu____8071 ty in
                FStar_Tactics_Monad.bind uu____8062
                  (fun uu____8083 ->
                     match uu____8083 with
                     | (ty1, uu____8093, guard) ->
                         let uu____8095 =
                           let uu____8098 = FStar_Tactics_Types.goal_env g in
                           proc_guard "change" uu____8098 guard in
                         FStar_Tactics_Monad.bind uu____8095
                           (fun uu____8101 ->
                              let uu____8102 =
                                let uu____8105 =
                                  FStar_Tactics_Types.goal_env g in
                                let uu____8106 =
                                  FStar_Tactics_Types.goal_type g in
                                do_unify uu____8105 uu____8106 ty1 in
                              FStar_Tactics_Monad.bind uu____8102
                                (fun bb ->
                                   if bb
                                   then
                                     let uu____8112 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1 in
                                     FStar_Tactics_Monad.replace_cur
                                       uu____8112
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops] in
                                      let ng =
                                        let uu____8118 =
                                          FStar_Tactics_Types.goal_env g in
                                        let uu____8119 =
                                          FStar_Tactics_Types.goal_type g in
                                        normalize steps uu____8118 uu____8119 in
                                      let nty =
                                        let uu____8121 =
                                          FStar_Tactics_Types.goal_env g in
                                        normalize steps uu____8121 ty1 in
                                      let uu____8122 =
                                        let uu____8125 =
                                          FStar_Tactics_Types.goal_env g in
                                        do_unify uu____8125 ng nty in
                                      FStar_Tactics_Monad.bind uu____8122
                                        (fun b ->
                                           if b
                                           then
                                             let uu____8131 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1 in
                                             FStar_Tactics_Monad.replace_cur
                                               uu____8131
                                           else
                                             FStar_Tactics_Monad.fail
                                               "not convertible"))))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "change") uu____8050
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
    let uu____8194 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____8212 =
             let uu____8221 = FStar_Tactics_Types.goal_env g in
             __tc uu____8221 s_tm in
           FStar_Tactics_Monad.bind uu____8212
             (fun uu____8239 ->
                match uu____8239 with
                | (s_tm1, s_ty, guard) ->
                    let uu____8257 =
                      let uu____8260 = FStar_Tactics_Types.goal_env g in
                      proc_guard "destruct" uu____8260 guard in
                    FStar_Tactics_Monad.bind uu____8257
                      (fun uu____8273 ->
                         let s_ty1 =
                           let uu____8275 = FStar_Tactics_Types.goal_env g in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant] uu____8275
                             s_ty in
                         let uu____8276 =
                           let uu____8291 = FStar_Syntax_Util.unrefine s_ty1 in
                           FStar_Syntax_Util.head_and_args' uu____8291 in
                         match uu____8276 with
                         | (h, args) ->
                             let uu____8322 =
                               let uu____8329 =
                                 let uu____8330 =
                                   FStar_Syntax_Subst.compress h in
                                 uu____8330.FStar_Syntax_Syntax.n in
                               match uu____8329 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   FStar_Tactics_Monad.ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____8345;
                                      FStar_Syntax_Syntax.vars = uu____8346;_},
                                    us)
                                   -> FStar_Tactics_Monad.ret (fv, us)
                               | uu____8356 ->
                                   FStar_Tactics_Monad.fail
                                     "type is not an fv" in
                             FStar_Tactics_Monad.bind uu____8322
                               (fun uu____8376 ->
                                  match uu____8376 with
                                  | (fv, a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv in
                                      let uu____8392 =
                                        let uu____8395 =
                                          FStar_Tactics_Types.goal_env g in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____8395 t_lid in
                                      (match uu____8392 with
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
                                                let uu____8434 =
                                                  erasable &&
                                                    (let uu____8436 =
                                                       FStar_Tactics_Types.is_irrelevant
                                                         g in
                                                     Prims.op_Negation
                                                       uu____8436) in
                                                failwhen uu____8434
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____8444 ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____8456 ->
                                                          let uu____8457 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty in
                                                          match uu____8457
                                                          with
                                                          | (t_ps1, t_ty1) ->
                                                              let uu____8472
                                                                =
                                                                FStar_Tactics_Monad.mapM
                                                                  (fun c_lid
                                                                    ->
                                                                    let uu____8500
                                                                    =
                                                                    let uu____8503
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____8503
                                                                    c_lid in
                                                                    match uu____8500
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
                                                                    uu____8576
                                                                    ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty in
                                                                    let uu____8581
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1) in
                                                                    match uu____8581
                                                                    with
                                                                    | 
                                                                    (c_us1,
                                                                    c_ty2) ->
                                                                    let uu____8604
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2 in
                                                                    (match uu____8604
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    comp) ->
                                                                    let uu____8623
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname in
                                                                    let ppname1
                                                                    =
                                                                    let uu____8646
                                                                    =
                                                                    let uu____8651
                                                                    =
                                                                    let uu____8652
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    ppname in
                                                                    Prims.op_Hat
                                                                    "a"
                                                                    uu____8652 in
                                                                    let uu____8653
                                                                    =
                                                                    FStar_Ident.range_of_id
                                                                    ppname in
                                                                    (uu____8651,
                                                                    uu____8653) in
                                                                    FStar_Ident.mk_ident
                                                                    uu____8646 in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    (let uu___1303_8656
                                                                    = bv in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1303_8656.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (uu___1303_8656.FStar_Syntax_Syntax.sort)
                                                                    }) in
                                                                    let bs' =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____8682
                                                                    ->
                                                                    match uu____8682
                                                                    with
                                                                    | 
                                                                    (bv, aq)
                                                                    ->
                                                                    let uu____8701
                                                                    =
                                                                    rename_bv
                                                                    bv in
                                                                    (uu____8701,
                                                                    aq)) bs in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun
                                                                    uu____8726
                                                                    ->
                                                                    fun
                                                                    uu____8727
                                                                    ->
                                                                    match 
                                                                    (uu____8726,
                                                                    uu____8727)
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____8753),
                                                                    (bv',
                                                                    uu____8755))
                                                                    ->
                                                                    let uu____8776
                                                                    =
                                                                    let uu____8783
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv' in
                                                                    (bv,
                                                                    uu____8783) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____8776)
                                                                    bs bs' in
                                                                    let uu____8788
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs' in
                                                                    let uu____8797
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst
                                                                    comp in
                                                                    (uu____8788,
                                                                    uu____8797) in
                                                                    (match uu____8623
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    comp1) ->
                                                                    let uu____8844
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    bs1 in
                                                                    (match uu____8844
                                                                    with
                                                                    | 
                                                                    (d_ps,
                                                                    bs2) ->
                                                                    let uu____8917
                                                                    =
                                                                    let uu____8918
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1 in
                                                                    Prims.op_Negation
                                                                    uu____8918 in
                                                                    failwhen
                                                                    uu____8917
                                                                    "not total?"
                                                                    (fun
                                                                    uu____8935
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
                                                                    uu___6_8951
                                                                    =
                                                                    match uu___6_8951
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____8954)
                                                                    -> true
                                                                    | 
                                                                    uu____8955
                                                                    -> false in
                                                                    let uu____8958
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args in
                                                                    match uu____8958
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
                                                                    uu____9093
                                                                    ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9155
                                                                    ->
                                                                    match uu____9155
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9175),
                                                                    (t,
                                                                    uu____9177))
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
                                                                    uu____9245
                                                                    ->
                                                                    match uu____9245
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9271),
                                                                    (t,
                                                                    uu____9273))
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
                                                                    uu____9328
                                                                    ->
                                                                    match uu____9328
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
                                                                    let uu____9378
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1362_9401
                                                                    = env1 in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.erasable_types_tab);
                                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___1362_9401.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                    }) s_ty1
                                                                    pat in
                                                                    match uu____9378
                                                                    with
                                                                    | 
                                                                    (uu____9414,
                                                                    uu____9415,
                                                                    uu____9416,
                                                                    uu____9417,
                                                                    pat_t,
                                                                    uu____9419,
                                                                    _guard_pat,
                                                                    _erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____9431
                                                                    =
                                                                    let uu____9432
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____9432 in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____9431 in
                                                                    let cod1
                                                                    =
                                                                    let uu____9436
                                                                    =
                                                                    let uu____9445
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b in
                                                                    [uu____9445] in
                                                                    let uu____9464
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____9436
                                                                    uu____9464 in
                                                                    let nty =
                                                                    let uu____9470
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu____9470 in
                                                                    let uu____9473
                                                                    =
                                                                    FStar_Tactics_Monad.new_uvar
                                                                    "destruct branch"
                                                                    env1 nty in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____9473
                                                                    (fun
                                                                    uu____9502
                                                                    ->
                                                                    match uu____9502
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
                                                                    let uu____9528
                                                                    =
                                                                    let uu____9539
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit in
                                                                    [uu____9539] in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____9528 in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1) in
                                                                    let uu____9575
                                                                    =
                                                                    let uu____9586
                                                                    =
                                                                    let uu____9591
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs3) in
                                                                    (fv1,
                                                                    uu____9591) in
                                                                    (g', br,
                                                                    uu____9586) in
                                                                    FStar_Tactics_Monad.ret
                                                                    uu____9575)))))))
                                                                    | 
                                                                    uu____9612
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids in
                                                              FStar_Tactics_Monad.bind
                                                                uu____8472
                                                                (fun goal_brs
                                                                   ->
                                                                   let uu____9661
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs in
                                                                   match uu____9661
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
                                                                    let uu____9734
                                                                    =
                                                                    solve' g
                                                                    w in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____9734
                                                                    (fun
                                                                    uu____9745
                                                                    ->
                                                                    let uu____9746
                                                                    =
                                                                    FStar_Tactics_Monad.add_goals
                                                                    goals in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____9746
                                                                    (fun
                                                                    uu____9756
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    infos)))))
                                            | uu____9763 ->
                                                FStar_Tactics_Monad.fail
                                                  "not an inductive type")))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "destruct") uu____8194
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9808::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9836 = init xs in x :: uu____9836
let rec (inspect :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Tactics_Monad.tac)
  =
  fun t ->
    let uu____9848 =
      let uu____9851 = top_env () in
      FStar_Tactics_Monad.bind uu____9851
        (fun e ->
           let t1 = FStar_Syntax_Util.unascribe t in
           let t2 = FStar_Syntax_Util.un_uinst t1 in
           let t3 = FStar_Syntax_Util.unlazy_emb t2 in
           match t3.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_meta (t4, uu____9867) -> inspect t4
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
               let uu____9932 = last args in
               (match uu____9932 with
                | (a, q) ->
                    let q' = FStar_Reflection_Basic.inspect_aqual q in
                    let uu____9962 =
                      let uu____9963 =
                        let uu____9968 =
                          let uu____9969 = init args in
                          FStar_Syntax_Syntax.mk_Tm_app hd uu____9969
                            t3.FStar_Syntax_Syntax.pos in
                        (uu____9968, (a, q')) in
                      FStar_Reflection_Data.Tv_App uu____9963 in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret uu____9962)
           | FStar_Syntax_Syntax.Tm_abs ([], uu____9980, uu____9981) ->
               failwith "empty arguments on Tm_abs"
           | FStar_Syntax_Syntax.Tm_abs (bs, t4, k) ->
               let uu____10033 = FStar_Syntax_Subst.open_term bs t4 in
               (match uu____10033 with
                | (bs1, t5) ->
                    (match bs1 with
                     | [] -> failwith "impossible"
                     | b::bs2 ->
                         let uu____10074 =
                           let uu____10075 =
                             let uu____10080 = FStar_Syntax_Util.abs bs2 t5 k in
                             (b, uu____10080) in
                           FStar_Reflection_Data.Tv_Abs uu____10075 in
                         FStar_All.pipe_left FStar_Tactics_Monad.ret
                           uu____10074))
           | FStar_Syntax_Syntax.Tm_type uu____10083 ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Type ())
           | FStar_Syntax_Syntax.Tm_arrow ([], k) ->
               failwith "empty binders on arrow"
           | FStar_Syntax_Syntax.Tm_arrow uu____10107 ->
               let uu____10122 = FStar_Syntax_Util.arrow_one t3 in
               (match uu____10122 with
                | FStar_Pervasives_Native.Some (b, c) ->
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Arrow (b, c))
                | FStar_Pervasives_Native.None -> failwith "impossible")
           | FStar_Syntax_Syntax.Tm_refine (bv, t4) ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____10152 = FStar_Syntax_Subst.open_term [b] t4 in
               (match uu____10152 with
                | (b', t5) ->
                    let b1 =
                      match b' with
                      | b'1::[] -> b'1
                      | uu____10205 -> failwith "impossible" in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Refine
                         ((FStar_Pervasives_Native.fst b1), t5)))
           | FStar_Syntax_Syntax.Tm_constant c ->
               let uu____10217 =
                 let uu____10218 = FStar_Reflection_Basic.inspect_const c in
                 FStar_Reflection_Data.Tv_Const uu____10218 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10217
           | FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
               let uu____10239 =
                 let uu____10240 =
                   let uu____10245 =
                     let uu____10246 =
                       FStar_Syntax_Unionfind.uvar_id
                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                     FStar_BigInt.of_int_fs uu____10246 in
                   (uu____10245, (ctx_u, s)) in
                 FStar_Reflection_Data.Tv_Uvar uu____10240 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10239
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____10280 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let b = FStar_Syntax_Syntax.mk_binder bv in
                      let uu____10285 = FStar_Syntax_Subst.open_term [b] t21 in
                      (match uu____10285 with
                       | (bs, t22) ->
                           let b1 =
                             match bs with
                             | b1::[] -> b1
                             | uu____10338 ->
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
                  | FStar_Util.Inr uu____10374 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let uu____10378 =
                        FStar_Syntax_Subst.open_let_rec [lb] t21 in
                      (match uu____10378 with
                       | (lbs, t22) ->
                           (match lbs with
                            | lb1::[] ->
                                (match lb1.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____10398 ->
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
                            | uu____10404 ->
                                failwith
                                  "impossible: open_term returned different amount of binders")))
           | FStar_Syntax_Syntax.Tm_match (t4, brs) ->
               let rec inspect_pat p =
                 match p.FStar_Syntax_Syntax.v with
                 | FStar_Syntax_Syntax.Pat_constant c ->
                     let uu____10458 = FStar_Reflection_Basic.inspect_const c in
                     FStar_Reflection_Data.Pat_Constant uu____10458
                 | FStar_Syntax_Syntax.Pat_cons (fv, ps) ->
                     let uu____10477 =
                       let uu____10488 =
                         FStar_List.map
                           (fun uu____10509 ->
                              match uu____10509 with
                              | (p1, b) ->
                                  let uu____10526 = inspect_pat p1 in
                                  (uu____10526, b)) ps in
                       (fv, uu____10488) in
                     FStar_Reflection_Data.Pat_Cons uu____10477
                 | FStar_Syntax_Syntax.Pat_var bv ->
                     FStar_Reflection_Data.Pat_Var bv
                 | FStar_Syntax_Syntax.Pat_wild bv ->
                     FStar_Reflection_Data.Pat_Wild bv
                 | FStar_Syntax_Syntax.Pat_dot_term (bv, t5) ->
                     FStar_Reflection_Data.Pat_Dot_Term (bv, t5) in
               let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
               let brs2 =
                 FStar_List.map
                   (fun uu___7_10620 ->
                      match uu___7_10620 with
                      | (pat, uu____10642, t5) ->
                          let uu____10660 = inspect_pat pat in
                          (uu____10660, t5)) brs1 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Match (t4, brs2))
           | FStar_Syntax_Syntax.Tm_unknown ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 FStar_Reflection_Data.Tv_Unknown
           | uu____10669 ->
               ((let uu____10671 =
                   let uu____10676 =
                     let uu____10677 = FStar_Syntax_Print.tag_of_term t3 in
                     let uu____10678 = term_to_string e t3 in
                     FStar_Util.format2
                       "inspect: outside of expected syntax (%s, %s)\n"
                       uu____10677 uu____10678 in
                   (FStar_Errors.Warning_CantInspect, uu____10676) in
                 FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos
                   uu____10671);
                FStar_All.pipe_left FStar_Tactics_Monad.ret
                  FStar_Reflection_Data.Tv_Unknown)) in
    FStar_Tactics_Monad.wrap_err "inspect" uu____9848
let (pack :
  FStar_Reflection_Data.term_view ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun tv ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10691 = FStar_Syntax_Syntax.bv_to_name bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10691
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10695 = FStar_Syntax_Syntax.bv_to_tm bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10695
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10699 = FStar_Syntax_Syntax.fv_to_tm fv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10699
    | FStar_Reflection_Data.Tv_App (l, (r, q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q in
        let uu____10706 = FStar_Syntax_Util.mk_app l [(r, q')] in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10706
    | FStar_Reflection_Data.Tv_Abs (b, t) ->
        let uu____10731 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10731
    | FStar_Reflection_Data.Tv_Arrow (b, c) ->
        let uu____10748 = FStar_Syntax_Util.arrow [b] c in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10748
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left FStar_Tactics_Monad.ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv, t) ->
        let uu____10767 = FStar_Syntax_Util.refine bv t in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10767
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10771 =
          let uu____10772 =
            let uu____10773 = FStar_Reflection_Basic.pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____10773 in
          FStar_Syntax_Syntax.mk uu____10772 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10771
    | FStar_Reflection_Data.Tv_Uvar (_u, ctx_u_s) ->
        let uu____10778 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10778
    | FStar_Reflection_Data.Tv_Let (false, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____10790 =
          let uu____10791 =
            let uu____10792 =
              let uu____10805 =
                let uu____10808 =
                  let uu____10809 = FStar_Syntax_Syntax.mk_binder bv in
                  [uu____10809] in
                FStar_Syntax_Subst.close uu____10808 t2 in
              ((false, [lb]), uu____10805) in
            FStar_Syntax_Syntax.Tm_let uu____10792 in
          FStar_Syntax_Syntax.mk uu____10791 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10790
    | FStar_Reflection_Data.Tv_Let (true, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____10849 = FStar_Syntax_Subst.close_let_rec [lb] t2 in
        (match uu____10849 with
         | (lbs, body) ->
             let uu____10864 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Range.dummyRange in
             FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10864)
    | FStar_Reflection_Data.Tv_Match (t, brs) ->
        let wrap v =
          {
            FStar_Syntax_Syntax.v = v;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10898 =
                let uu____10899 = FStar_Reflection_Basic.pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____10899 in
              FStar_All.pipe_left wrap uu____10898
          | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
              let uu____10914 =
                let uu____10915 =
                  let uu____10928 =
                    FStar_List.map
                      (fun uu____10949 ->
                         match uu____10949 with
                         | (p1, b) ->
                             let uu____10960 = pack_pat p1 in
                             (uu____10960, b)) ps in
                  (fv, uu____10928) in
                FStar_Syntax_Syntax.Pat_cons uu____10915 in
              FStar_All.pipe_left wrap uu____10914
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv, t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1)) in
        let brs1 =
          FStar_List.map
            (fun uu___8_11006 ->
               match uu___8_11006 with
               | (pat, t1) ->
                   let uu____11023 = pack_pat pat in
                   (uu____11023, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        let uu____11071 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11071
    | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
        let uu____11099 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11099
    | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
        let uu____11145 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11145
    | FStar_Reflection_Data.Tv_Unknown ->
        let uu____11184 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11184
let (lget :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun k ->
      let uu____11201 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps ->
             let uu____11207 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k in
             match uu____11207 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lget") uu____11201
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun _ty ->
    fun k ->
      fun t ->
        let uu____11236 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let ps1 =
                 let uu___1667_11243 = ps in
                 let uu____11244 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___1667_11243.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___1667_11243.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___1667_11243.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___1667_11243.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___1667_11243.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___1667_11243.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___1667_11243.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___1667_11243.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___1667_11243.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___1667_11243.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___1667_11243.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____11244
                 } in
               FStar_Tactics_Monad.set ps1) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lset") uu____11236
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env1 ->
    fun typ ->
      let uu____11269 =
        FStar_TypeChecker_Env.new_implicit_var_aux "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env1 typ
          FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None in
      match uu____11269 with
      | (u, ctx_uvars, g_u) ->
          let uu____11301 = FStar_List.hd ctx_uvars in
          (match uu____11301 with
           | (ctx_uvar, uu____11315) ->
               let g =
                 let uu____11317 = FStar_Options.peek () in
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar uu____11317 false
                   "" in
               (g, g_u))
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env1 ->
    let uu____11323 = FStar_TypeChecker_Env.clear_expected_typ env1 in
    match uu____11323 with
    | (env2, uu____11331) ->
        let env3 =
          let uu___1684_11337 = env2 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1684_11337.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1684_11337.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1684_11337.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1684_11337.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1684_11337.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1684_11337.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1684_11337.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1684_11337.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1684_11337.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1684_11337.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___1684_11337.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1684_11337.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1684_11337.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1684_11337.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1684_11337.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1684_11337.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1684_11337.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1684_11337.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1684_11337.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1684_11337.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1684_11337.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1684_11337.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1684_11337.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1684_11337.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1684_11337.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1684_11337.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1684_11337.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1684_11337.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1684_11337.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1684_11337.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1684_11337.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1684_11337.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1684_11337.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1684_11337.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1684_11337.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1684_11337.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1684_11337.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1684_11337.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1684_11337.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1684_11337.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1684_11337.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1684_11337.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1684_11337.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1684_11337.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1684_11337.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1684_11337.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        let env4 =
          let uu___1687_11339 = env3 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1687_11339.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1687_11339.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1687_11339.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1687_11339.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1687_11339.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1687_11339.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1687_11339.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1687_11339.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1687_11339.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1687_11339.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1687_11339.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1687_11339.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1687_11339.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1687_11339.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1687_11339.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1687_11339.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1687_11339.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1687_11339.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1687_11339.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1687_11339.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1687_11339.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1687_11339.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1687_11339.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___1687_11339.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1687_11339.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1687_11339.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1687_11339.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1687_11339.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1687_11339.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1687_11339.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1687_11339.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1687_11339.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1687_11339.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1687_11339.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1687_11339.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1687_11339.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1687_11339.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1687_11339.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1687_11339.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1687_11339.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1687_11339.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1687_11339.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1687_11339.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1687_11339.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1687_11339.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1687_11339.FStar_TypeChecker_Env.enable_defer_to_tac)
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
            let uu____11370 =
              FStar_TypeChecker_Env.debug env2
                (FStar_Options.Other "TacVerbose") in
            let uu____11371 = FStar_Util.psmap_empty () in
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
              FStar_Tactics_Types.tac_verb_dbg = uu____11370;
              FStar_Tactics_Types.local_state = uu____11371
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
        let uu____11394 = goal_of_goal_ty env2 typ in
        match uu____11394 with
        | (g, g_u) ->
            let ps =
              proofstate_of_goals rng env2 [g]
                g_u.FStar_TypeChecker_Common.implicits in
            let uu____11406 = FStar_Tactics_Types.goal_witness g in
            (ps, uu____11406)
let (goal_of_implicit :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicit -> FStar_Tactics_Types.goal)
  =
  fun env1 ->
    fun i ->
      let uu____11417 = FStar_Options.peek () in
      FStar_Tactics_Types.mk_goal
        (let uu___1706_11420 = env1 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1706_11420.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1706_11420.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1706_11420.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             ((i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1706_11420.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1706_11420.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1706_11420.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1706_11420.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1706_11420.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1706_11420.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1706_11420.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1706_11420.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1706_11420.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1706_11420.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1706_11420.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1706_11420.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1706_11420.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___1706_11420.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___1706_11420.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___1706_11420.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___1706_11420.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1706_11420.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1706_11420.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1706_11420.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1706_11420.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1706_11420.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1706_11420.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1706_11420.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1706_11420.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1706_11420.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1706_11420.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1706_11420.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1706_11420.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1706_11420.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1706_11420.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1706_11420.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1706_11420.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1706_11420.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___1706_11420.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___1706_11420.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1706_11420.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1706_11420.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1706_11420.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1706_11420.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1706_11420.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1706_11420.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___1706_11420.FStar_TypeChecker_Env.enable_defer_to_tac)
         }) i.FStar_TypeChecker_Common.imp_uvar uu____11417 false
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
        let goals = FStar_List.map (goal_of_implicit env1) imps in
        let w =
          let uu____11444 = FStar_List.hd goals in
          FStar_Tactics_Types.goal_witness uu____11444 in
        let ps =
          let uu____11446 =
            FStar_TypeChecker_Env.debug env1
              (FStar_Options.Other "TacVerbose") in
          let uu____11447 = FStar_Util.psmap_empty () in
          {
            FStar_Tactics_Types.main_context = env1;
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
            FStar_Tactics_Types.tac_verb_dbg = uu____11446;
            FStar_Tactics_Types.local_state = uu____11447
          } in
        (ps, w)