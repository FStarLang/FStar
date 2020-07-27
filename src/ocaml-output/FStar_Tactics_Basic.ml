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
let (do_dump_ps : Prims.string -> FStar_Tactics_Types.proofstate -> unit) =
  fun msg ->
    fun ps ->
      let psc = ps.FStar_Tactics_Types.psc in
      let subst = FStar_TypeChecker_Cfg.psc_subst psc in
      let uu____152 = FStar_Tactics_Types.subst_proof_state subst ps in
      FStar_Tactics_Printing.do_dump_proofstate uu____152 msg
let (dump : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    FStar_Tactics_Monad.mk_tac
      (fun ps -> do_dump_ps msg ps; FStar_Tactics_Result.Success ((), ps))
let (dump_all : Prims.bool -> Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun print_resolved ->
    fun msg ->
      FStar_Tactics_Monad.mk_tac
        (fun ps ->
           let gs =
             FStar_List.map
               (fun i ->
                  FStar_Tactics_Types.goal_of_implicit
                    ps.FStar_Tactics_Types.main_context i)
               ps.FStar_Tactics_Types.all_implicits in
           let gs1 =
             if print_resolved
             then gs
             else
               FStar_List.filter
                 (fun g ->
                    let uu____200 = FStar_Tactics_Types.check_goal_solved g in
                    Prims.op_Negation uu____200) gs in
           let ps' =
             let uu___49_202 = ps in
             {
               FStar_Tactics_Types.main_context =
                 (uu___49_202.FStar_Tactics_Types.main_context);
               FStar_Tactics_Types.all_implicits =
                 (uu___49_202.FStar_Tactics_Types.all_implicits);
               FStar_Tactics_Types.goals = gs1;
               FStar_Tactics_Types.smt_goals = [];
               FStar_Tactics_Types.depth =
                 (uu___49_202.FStar_Tactics_Types.depth);
               FStar_Tactics_Types.__dump =
                 (uu___49_202.FStar_Tactics_Types.__dump);
               FStar_Tactics_Types.psc =
                 (uu___49_202.FStar_Tactics_Types.psc);
               FStar_Tactics_Types.entry_range =
                 (uu___49_202.FStar_Tactics_Types.entry_range);
               FStar_Tactics_Types.guard_policy =
                 (uu___49_202.FStar_Tactics_Types.guard_policy);
               FStar_Tactics_Types.freshness =
                 (uu___49_202.FStar_Tactics_Types.freshness);
               FStar_Tactics_Types.tac_verb_dbg =
                 (uu___49_202.FStar_Tactics_Types.tac_verb_dbg);
               FStar_Tactics_Types.local_state =
                 (uu___49_202.FStar_Tactics_Types.local_state)
             } in
           do_dump_ps msg ps'; FStar_Tactics_Result.Success ((), ps))
let fail1 :
  'uuuuuu210 .
    Prims.string -> Prims.string -> 'uuuuuu210 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      let uu____223 = FStar_Util.format1 msg x in
      FStar_Tactics_Monad.fail uu____223
let fail2 :
  'uuuuuu232 .
    Prims.string ->
      Prims.string -> Prims.string -> 'uuuuuu232 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        let uu____250 = FStar_Util.format2 msg x y in
        FStar_Tactics_Monad.fail uu____250
let fail3 :
  'uuuuuu261 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> 'uuuuuu261 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          let uu____284 = FStar_Util.format3 msg x y z in
          FStar_Tactics_Monad.fail uu____284
let fail4 :
  'uuuuuu297 .
    Prims.string ->
      Prims.string ->
        Prims.string ->
          Prims.string -> Prims.string -> 'uuuuuu297 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          fun w ->
            let uu____325 = FStar_Util.format4 msg x y z w in
            FStar_Tactics_Monad.fail uu____325
let catch :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (Prims.exn, 'a) FStar_Util.either FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____358 = FStar_Tactics_Monad.run t ps in
         match uu____358 with
         | FStar_Tactics_Result.Success (a1, q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a1), q))
         | FStar_Tactics_Result.Failed (m, q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___82_382 = ps in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___82_382.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___82_382.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___82_382.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___82_382.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___82_382.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___82_382.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___82_382.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___82_382.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___82_382.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___82_382.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___82_382.FStar_Tactics_Types.local_state)
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
         let uu____420 = FStar_Tactics_Monad.run t ps in
         match uu____420 with
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
    let uu____467 = catch t in
    FStar_Tactics_Monad.bind uu____467
      (fun r ->
         match r with
         | FStar_Util.Inr v ->
             FStar_Tactics_Monad.ret (FStar_Pervasives_Native.Some v)
         | FStar_Util.Inl uu____494 ->
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
           (fun uu___108_525 ->
              match () with
              | () ->
                  let uu____530 = trytac t in
                  FStar_Tactics_Monad.run uu____530 ps) ()
         with
         | FStar_Errors.Err (uu____546, msg) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____550 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____555, msg, uu____557) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____560 ->
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
        (let uu____585 =
           FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "1346") in
         if uu____585
         then
           let uu____586 = FStar_Syntax_Print.term_to_string t1 in
           let uu____587 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____586
             uu____587
         else ());
        (try
           (fun uu___128_594 ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env1 t1 t2 in
                  ((let uu____601 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "1346") in
                    if uu____601
                    then
                      let uu____602 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env1) res in
                      let uu____603 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____604 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____602
                        uu____603 uu____604
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____609 =
                          FStar_Tactics_Monad.add_implicits
                            g.FStar_TypeChecker_Common.implicits in
                        FStar_Tactics_Monad.bind uu____609
                          (fun uu____613 -> FStar_Tactics_Monad.ret true))))
             ()
         with
         | FStar_Errors.Err (uu____620, msg) ->
             FStar_Tactics_Monad.mlog
               (fun uu____623 ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____625 -> FStar_Tactics_Monad.ret false)
         | FStar_Errors.Error (uu____626, msg, r) ->
             FStar_Tactics_Monad.mlog
               (fun uu____631 ->
                  let uu____632 = FStar_Range.string_of_range r in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____632)
               (fun uu____634 -> FStar_Tactics_Monad.ret false))
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____657 ->
             (let uu____659 =
                FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "1346") in
              if uu____659
              then
                (FStar_Options.push ();
                 (let uu____661 =
                    FStar_Options.set_options
                      "--debug_level Rel --debug_level RelCheck" in
                  ()))
              else ());
             (let uu____663 = __do_unify env1 t1 t2 in
              FStar_Tactics_Monad.bind uu____663
                (fun r ->
                   (let uu____670 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "1346") in
                    if uu____670 then FStar_Options.pop () else ());
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
        let uu____694 = do_unify env1 t1 t2 in
        FStar_Tactics_Monad.bind uu____694
          (fun r ->
             if r
             then
               let uvs2 = FStar_Syntax_Free.uvars_uncached t1 in
               let uu____706 =
                 let uu____707 = FStar_Util.set_eq uvs1 uvs2 in
                 Prims.op_Negation uu____707 in
               (if uu____706
                then FStar_Tactics_Monad.ret false
                else FStar_Tactics_Monad.ret true)
             else FStar_Tactics_Monad.ret false)
let (set_solution :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____726 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
      match uu____726 with
      | FStar_Pervasives_Native.Some uu____731 ->
          let uu____732 =
            let uu____733 =
              FStar_Tactics_Printing.goal_to_string_verbose goal in
            FStar_Util.format1 "Goal %s is already solved" uu____733 in
          FStar_Tactics_Monad.fail uu____732
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
      let uu____749 = FStar_Tactics_Types.goal_env goal in
      let uu____750 = FStar_Tactics_Types.goal_witness goal in
      do_unify uu____749 solution uu____750
let (solve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let e = FStar_Tactics_Types.goal_env goal in
      FStar_Tactics_Monad.mlog
        (fun uu____769 ->
           let uu____770 =
             let uu____771 = FStar_Tactics_Types.goal_witness goal in
             FStar_Syntax_Print.term_to_string uu____771 in
           let uu____772 = FStar_Syntax_Print.term_to_string solution in
           FStar_Util.print2 "solve %s := %s\n" uu____770 uu____772)
        (fun uu____775 ->
           let uu____776 = trysolve goal solution in
           FStar_Tactics_Monad.bind uu____776
             (fun b ->
                if b
                then
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____784 -> FStar_Tactics_Monad.remove_solved_goals)
                else
                  (let uu____786 =
                     let uu____787 =
                       let uu____788 = FStar_Tactics_Types.goal_env goal in
                       tts uu____788 solution in
                     let uu____789 =
                       let uu____790 = FStar_Tactics_Types.goal_env goal in
                       let uu____791 = FStar_Tactics_Types.goal_witness goal in
                       tts uu____790 uu____791 in
                     let uu____792 =
                       let uu____793 = FStar_Tactics_Types.goal_env goal in
                       let uu____794 = FStar_Tactics_Types.goal_type goal in
                       tts uu____793 uu____794 in
                     FStar_Util.format3 "%s does not solve %s : %s" uu____787
                       uu____789 uu____792 in
                   FStar_Tactics_Monad.fail uu____786)))
let (solve' :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____809 = set_solution goal solution in
      FStar_Tactics_Monad.bind uu____809
        (fun uu____813 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
             (fun uu____815 -> FStar_Tactics_Monad.remove_solved_goals))
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____822 = FStar_Syntax_Util.un_squash t1 in
    match uu____822 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t' in
        let uu____833 =
          let uu____834 = FStar_Syntax_Subst.compress t'1 in
          uu____834.FStar_Syntax_Syntax.n in
        (match uu____833 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____838 -> false)
    | uu____839 -> false
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____849 = FStar_Syntax_Util.un_squash t in
    match uu____849 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____859 =
          let uu____860 = FStar_Syntax_Subst.compress t' in
          uu____860.FStar_Syntax_Syntax.n in
        (match uu____859 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____864 -> false)
    | uu____865 -> false
let (tadmit_t : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____879 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                (let uu____888 =
                   let uu____889 = FStar_Tactics_Types.goal_type g in
                   uu____889.FStar_Syntax_Syntax.pos in
                 let uu____892 =
                   let uu____897 =
                     let uu____898 =
                       FStar_Tactics_Printing.goal_to_string ""
                         FStar_Pervasives_Native.None ps g in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____898 in
                   (FStar_Errors.Warning_TacAdmit, uu____897) in
                 FStar_Errors.log_issue uu____888 uu____892);
                solve' g t)) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tadmit_t") uu____879
let (fresh : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____913 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let n = ps.FStar_Tactics_Types.freshness in
         let ps1 =
           let uu___214_923 = ps in
           {
             FStar_Tactics_Types.main_context =
               (uu___214_923.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (uu___214_923.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___214_923.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___214_923.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___214_923.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___214_923.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (uu___214_923.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___214_923.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___214_923.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___214_923.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___214_923.FStar_Tactics_Types.local_state)
           } in
         let uu____924 = FStar_Tactics_Monad.set ps1 in
         FStar_Tactics_Monad.bind uu____924
           (fun uu____929 ->
              let uu____930 = FStar_BigInt.of_int_fs n in
              FStar_Tactics_Monad.ret uu____930))
let (curms : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____937 ->
    let uu____940 =
      let uu____941 = FStar_Util.now_ms () in
      FStar_All.pipe_right uu____941 FStar_BigInt.of_int_fs in
    FStar_Tactics_Monad.ret uu____940
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
             (fun uu____984 ->
                let uu____985 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____985)
             (fun uu____988 ->
                let e1 =
                  let uu___223_990 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___223_990.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___223_990.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___223_990.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___223_990.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___223_990.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___223_990.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___223_990.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___223_990.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___223_990.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___223_990.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___223_990.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___223_990.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___223_990.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___223_990.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___223_990.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___223_990.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___223_990.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___223_990.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___223_990.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___223_990.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___223_990.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___223_990.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___223_990.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___223_990.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___223_990.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___223_990.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___223_990.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___223_990.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___223_990.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___223_990.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___223_990.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___223_990.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___223_990.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___223_990.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___223_990.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___223_990.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___223_990.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___223_990.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___223_990.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___223_990.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___223_990.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___223_990.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___223_990.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___223_990.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___223_990.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___223_990.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___227_1001 ->
                     match () with
                     | () ->
                         let uu____1010 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t in
                         FStar_Tactics_Monad.ret uu____1010) ()
                with
                | FStar_Errors.Err (uu____1037, msg) ->
                    let uu____1039 = tts e1 t in
                    let uu____1040 =
                      let uu____1041 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1041
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1039 uu____1040 msg
                | FStar_Errors.Error (uu____1048, msg, uu____1050) ->
                    let uu____1051 = tts e1 t in
                    let uu____1052 =
                      let uu____1053 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1053
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1051 uu____1052 msg))
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
             (fun uu____1102 ->
                let uu____1103 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____1103)
             (fun uu____1106 ->
                let e1 =
                  let uu___244_1108 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___244_1108.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___244_1108.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___244_1108.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___244_1108.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___244_1108.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___244_1108.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___244_1108.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___244_1108.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___244_1108.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___244_1108.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___244_1108.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___244_1108.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___244_1108.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___244_1108.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___244_1108.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___244_1108.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___244_1108.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___244_1108.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___244_1108.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___244_1108.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___244_1108.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___244_1108.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___244_1108.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___244_1108.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___244_1108.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___244_1108.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___244_1108.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___244_1108.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___244_1108.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___244_1108.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___244_1108.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___244_1108.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___244_1108.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___244_1108.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___244_1108.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___244_1108.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___244_1108.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___244_1108.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___244_1108.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___244_1108.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___244_1108.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___244_1108.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___244_1108.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___244_1108.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___244_1108.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___244_1108.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___248_1122 ->
                     match () with
                     | () ->
                         let uu____1131 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t in
                         (match uu____1131 with
                          | (t1, lc, g) ->
                              FStar_Tactics_Monad.ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu____1169, msg) ->
                    let uu____1171 = tts e1 t in
                    let uu____1172 =
                      let uu____1173 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1173
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1171 uu____1172 msg
                | FStar_Errors.Error (uu____1180, msg, uu____1182) ->
                    let uu____1183 = tts e1 t in
                    let uu____1184 =
                      let uu____1185 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1185
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1183 uu____1184 msg))
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
             (fun uu____1234 ->
                let uu____1235 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_lax(%s)\n" uu____1235)
             (fun uu____1239 ->
                let e1 =
                  let uu___269_1241 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___269_1241.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___269_1241.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___269_1241.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___269_1241.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___269_1241.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___269_1241.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___269_1241.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___269_1241.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___269_1241.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___269_1241.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___269_1241.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___269_1241.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___269_1241.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___269_1241.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___269_1241.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___269_1241.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___269_1241.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___269_1241.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___269_1241.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___269_1241.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___269_1241.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___269_1241.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___269_1241.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___269_1241.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___269_1241.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___269_1241.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___269_1241.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___269_1241.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___269_1241.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___269_1241.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___269_1241.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___269_1241.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___269_1241.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___269_1241.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___269_1241.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___269_1241.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___269_1241.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___269_1241.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___269_1241.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___269_1241.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___269_1241.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___269_1241.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___269_1241.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___269_1241.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___269_1241.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___269_1241.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                let e2 =
                  let uu___272_1243 = e1 in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___272_1243.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___272_1243.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___272_1243.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___272_1243.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___272_1243.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___272_1243.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___272_1243.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___272_1243.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___272_1243.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___272_1243.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___272_1243.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___272_1243.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___272_1243.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___272_1243.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___272_1243.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___272_1243.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___272_1243.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___272_1243.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___272_1243.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___272_1243.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___272_1243.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___272_1243.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___272_1243.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___272_1243.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___272_1243.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___272_1243.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___272_1243.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___272_1243.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___272_1243.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___272_1243.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___272_1243.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___272_1243.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___272_1243.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___272_1243.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___272_1243.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___272_1243.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___272_1243.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___272_1243.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___272_1243.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___272_1243.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___272_1243.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___272_1243.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___272_1243.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___272_1243.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___272_1243.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___272_1243.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___276_1254 ->
                     match () with
                     | () ->
                         let uu____1263 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t in
                         FStar_Tactics_Monad.ret uu____1263) ()
                with
                | FStar_Errors.Err (uu____1290, msg) ->
                    let uu____1292 = tts e2 t in
                    let uu____1293 =
                      let uu____1294 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1294
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1292 uu____1293 msg
                | FStar_Errors.Error (uu____1301, msg, uu____1303) ->
                    let uu____1304 = tts e2 t in
                    let uu____1305 =
                      let uu____1306 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1306
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1304 uu____1305 msg))
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
  fun uu____1333 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps -> FStar_Tactics_Monad.ret ps.FStar_Tactics_Types.guard_policy)
let (set_guard_policy :
  FStar_Tactics_Types.guard_policy -> unit FStar_Tactics_Monad.tac) =
  fun pol ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_Tactics_Monad.set
           (let uu___297_1351 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___297_1351.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___297_1351.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___297_1351.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___297_1351.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___297_1351.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___297_1351.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___297_1351.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___297_1351.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___297_1351.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___297_1351.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___297_1351.FStar_Tactics_Types.local_state)
            }))
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun pol ->
    fun t ->
      let uu____1375 = get_guard_policy () in
      FStar_Tactics_Monad.bind uu____1375
        (fun old_pol ->
           let uu____1381 = set_guard_policy pol in
           FStar_Tactics_Monad.bind uu____1381
             (fun uu____1385 ->
                FStar_Tactics_Monad.bind t
                  (fun r ->
                     let uu____1389 = set_guard_policy old_pol in
                     FStar_Tactics_Monad.bind uu____1389
                       (fun uu____1393 -> FStar_Tactics_Monad.ret r))))
let (getopts : FStar_Options.optionstate FStar_Tactics_Monad.tac) =
  let uu____1396 = trytac FStar_Tactics_Monad.cur_goal in
  FStar_Tactics_Monad.bind uu____1396
    (fun uu___0_1405 ->
       match uu___0_1405 with
       | FStar_Pervasives_Native.Some g ->
           FStar_Tactics_Monad.ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None ->
           let uu____1411 = FStar_Options.peek () in
           FStar_Tactics_Monad.ret uu____1411)
let (proc_guard :
  Prims.string ->
    env -> FStar_TypeChecker_Common.guard_t -> unit FStar_Tactics_Monad.tac)
  =
  fun reason ->
    fun e ->
      fun g ->
        FStar_Tactics_Monad.mlog
          (fun uu____1433 ->
             let uu____1434 = FStar_TypeChecker_Rel.guard_to_string e g in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____1434)
          (fun uu____1437 ->
             let uu____1438 =
               FStar_Tactics_Monad.add_implicits
                 g.FStar_TypeChecker_Common.implicits in
             FStar_Tactics_Monad.bind uu____1438
               (fun uu____1442 ->
                  FStar_Tactics_Monad.bind getopts
                    (fun opts ->
                       let uu____1446 =
                         let uu____1447 =
                           FStar_TypeChecker_Rel.simplify_guard e g in
                         uu____1447.FStar_TypeChecker_Common.guard_f in
                       match uu____1446 with
                       | FStar_TypeChecker_Common.Trivial ->
                           FStar_Tactics_Monad.ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____1451 = istrivial e f in
                           if uu____1451
                           then FStar_Tactics_Monad.ret ()
                           else
                             FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
                               (fun ps ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop ->
                                      ((let uu____1461 =
                                          let uu____1466 =
                                            let uu____1467 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____1467 in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____1466) in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____1461);
                                       FStar_Tactics_Monad.ret ())
                                  | FStar_Tactics_Types.Goal ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1470 ->
                                           let uu____1471 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____1471)
                                        (fun uu____1474 ->
                                           let uu____1475 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts "" in
                                           FStar_Tactics_Monad.bind
                                             uu____1475
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___326_1482 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___326_1482.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___326_1482.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___326_1482.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___326_1482.FStar_Tactics_Types.label)
                                                  } in
                                                FStar_Tactics_Monad.push_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.SMT ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1485 ->
                                           let uu____1486 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____1486)
                                        (fun uu____1489 ->
                                           let uu____1490 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts "" in
                                           FStar_Tactics_Monad.bind
                                             uu____1490
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___333_1497 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___333_1497.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___333_1497.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___333_1497.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___333_1497.FStar_Tactics_Types.label)
                                                  } in
                                                FStar_Tactics_Monad.push_smt_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.Force ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1500 ->
                                           let uu____1501 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____1501)
                                        (fun uu____1503 ->
                                           try
                                             (fun uu___340_1508 ->
                                                match () with
                                                | () ->
                                                    let uu____1511 =
                                                      let uu____1512 =
                                                        let uu____1513 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____1513 in
                                                      Prims.op_Negation
                                                        uu____1512 in
                                                    if uu____1511
                                                    then
                                                      FStar_Tactics_Monad.mlog
                                                        (fun uu____1518 ->
                                                           let uu____1519 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____1519)
                                                        (fun uu____1521 ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else
                                                      FStar_Tactics_Monad.ret
                                                        ()) ()
                                           with
                                           | uu___339_1524 ->
                                               FStar_Tactics_Monad.mlog
                                                 (fun uu____1529 ->
                                                    let uu____1530 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____1530)
                                                 (fun uu____1532 ->
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
      let uu____1547 =
        let uu____1550 = __tc_lax e t in
        FStar_Tactics_Monad.bind uu____1550
          (fun uu____1570 ->
             match uu____1570 with
             | (uu____1579, lc, uu____1581) ->
                 let uu____1582 =
                   let uu____1583 = FStar_TypeChecker_Common.lcomp_comp lc in
                   FStar_All.pipe_right uu____1583
                     FStar_Pervasives_Native.fst in
                 FStar_Tactics_Monad.ret uu____1582) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tcc") uu____1547
let (tc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Reflection_Data.typ FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu____1610 =
        let uu____1615 = tcc e t in
        FStar_Tactics_Monad.bind uu____1615
          (fun c -> FStar_Tactics_Monad.ret (FStar_Syntax_Util.comp_result c)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tc") uu____1610
let (trivial : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____1638 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____1644 =
           let uu____1645 = FStar_Tactics_Types.goal_env goal in
           let uu____1646 = FStar_Tactics_Types.goal_type goal in
           istrivial uu____1645 uu____1646 in
         if uu____1644
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____1650 =
              let uu____1651 = FStar_Tactics_Types.goal_env goal in
              let uu____1652 = FStar_Tactics_Types.goal_type goal in
              tts uu____1651 uu____1652 in
            fail1 "Not a trivial goal: %s" uu____1650))
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
             let uu____1701 =
               try
                 (fun uu___391_1724 ->
                    match () with
                    | () ->
                        let uu____1735 =
                          let uu____1744 = FStar_BigInt.to_int_fs n in
                          FStar_List.splitAt uu____1744
                            p.FStar_Tactics_Types.goals in
                        FStar_Tactics_Monad.ret uu____1735) ()
               with
               | uu___390_1754 ->
                   FStar_Tactics_Monad.fail "divide: not enough goals" in
             FStar_Tactics_Monad.bind uu____1701
               (fun uu____1790 ->
                  match uu____1790 with
                  | (lgs, rgs) ->
                      let lp =
                        let uu___373_1816 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___373_1816.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___373_1816.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___373_1816.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___373_1816.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___373_1816.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___373_1816.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___373_1816.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___373_1816.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___373_1816.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___373_1816.FStar_Tactics_Types.local_state)
                        } in
                      let uu____1817 = FStar_Tactics_Monad.set lp in
                      FStar_Tactics_Monad.bind uu____1817
                        (fun uu____1825 ->
                           FStar_Tactics_Monad.bind l
                             (fun a1 ->
                                FStar_Tactics_Monad.bind
                                  FStar_Tactics_Monad.get
                                  (fun lp' ->
                                     let rp =
                                       let uu___379_1841 = lp' in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___379_1841.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___379_1841.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___379_1841.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___379_1841.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___379_1841.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___379_1841.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___379_1841.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___379_1841.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___379_1841.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___379_1841.FStar_Tactics_Types.local_state)
                                       } in
                                     let uu____1842 =
                                       FStar_Tactics_Monad.set rp in
                                     FStar_Tactics_Monad.bind uu____1842
                                       (fun uu____1850 ->
                                          FStar_Tactics_Monad.bind r
                                            (fun b1 ->
                                               FStar_Tactics_Monad.bind
                                                 FStar_Tactics_Monad.get
                                                 (fun rp' ->
                                                    let p' =
                                                      let uu___385_1866 = rp' in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___385_1866.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___385_1866.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___385_1866.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___385_1866.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___385_1866.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___385_1866.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___385_1866.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___385_1866.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___385_1866.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___385_1866.FStar_Tactics_Types.local_state)
                                                      } in
                                                    let uu____1867 =
                                                      FStar_Tactics_Monad.set
                                                        p' in
                                                    FStar_Tactics_Monad.bind
                                                      uu____1867
                                                      (fun uu____1875 ->
                                                         FStar_Tactics_Monad.bind
                                                           FStar_Tactics_Monad.remove_solved_goals
                                                           (fun uu____1881 ->
                                                              FStar_Tactics_Monad.ret
                                                                (a1, b1)))))))))))
let focus : 'a . 'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac =
  fun f ->
    let uu____1902 = divide FStar_BigInt.one f FStar_Tactics_Monad.idtac in
    FStar_Tactics_Monad.bind uu____1902
      (fun uu____1915 ->
         match uu____1915 with | (a1, ()) -> FStar_Tactics_Monad.ret a1)
let rec map :
  'a . 'a FStar_Tactics_Monad.tac -> 'a Prims.list FStar_Tactics_Monad.tac =
  fun tau ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun p ->
         match p.FStar_Tactics_Types.goals with
         | [] -> FStar_Tactics_Monad.ret []
         | uu____1952::uu____1953 ->
             let uu____1956 =
               let uu____1965 = map tau in
               divide FStar_BigInt.one tau uu____1965 in
             FStar_Tactics_Monad.bind uu____1956
               (fun uu____1983 ->
                  match uu____1983 with
                  | (h, t) -> FStar_Tactics_Monad.ret (h :: t)))
let (seq :
  unit FStar_Tactics_Monad.tac ->
    unit FStar_Tactics_Monad.tac -> unit FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let uu____2024 =
        FStar_Tactics_Monad.bind t1
          (fun uu____2029 ->
             let uu____2030 = map t2 in
             FStar_Tactics_Monad.bind uu____2030
               (fun uu____2038 -> FStar_Tactics_Monad.ret ())) in
      focus uu____2024
let (intro : unit -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac) =
  fun uu____2047 ->
    let uu____2050 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____2059 =
             let uu____2066 =
               let uu____2067 = FStar_Tactics_Types.goal_env goal in
               let uu____2068 = FStar_Tactics_Types.goal_type goal in
               whnf uu____2067 uu____2068 in
             FStar_Syntax_Util.arrow_one uu____2066 in
           match uu____2059 with
           | FStar_Pervasives_Native.Some (b, c) ->
               let uu____2077 =
                 let uu____2078 = FStar_Syntax_Util.is_total_comp c in
                 Prims.op_Negation uu____2078 in
               if uu____2077
               then FStar_Tactics_Monad.fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2083 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.push_binders uu____2083 [b] in
                  let typ' = FStar_Syntax_Util.comp_result c in
                  let uu____2099 =
                    FStar_Tactics_Monad.new_uvar "intro" env' typ' in
                  FStar_Tactics_Monad.bind uu____2099
                    (fun uu____2115 ->
                       match uu____2115 with
                       | (body, ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)) in
                           let uu____2139 = set_solution goal sol in
                           FStar_Tactics_Monad.bind uu____2139
                             (fun uu____2145 ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label in
                                let uu____2147 =
                                  let uu____2150 = bnorm_goal g in
                                  FStar_Tactics_Monad.replace_cur uu____2150 in
                                FStar_Tactics_Monad.bind uu____2147
                                  (fun uu____2152 ->
                                     FStar_Tactics_Monad.ret b))))
           | FStar_Pervasives_Native.None ->
               let uu____2157 =
                 let uu____2158 = FStar_Tactics_Types.goal_env goal in
                 let uu____2159 = FStar_Tactics_Types.goal_type goal in
                 tts uu____2158 uu____2159 in
               fail1 "goal is not an arrow (%s)" uu____2157) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "intro") uu____2050
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder)
      FStar_Tactics_Monad.tac)
  =
  fun uu____2174 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2195 =
            let uu____2202 =
              let uu____2203 = FStar_Tactics_Types.goal_env goal in
              let uu____2204 = FStar_Tactics_Types.goal_type goal in
              whnf uu____2203 uu____2204 in
            FStar_Syntax_Util.arrow_one uu____2202 in
          match uu____2195 with
          | FStar_Pervasives_Native.Some (b, c) ->
              let uu____2217 =
                let uu____2218 = FStar_Syntax_Util.is_total_comp c in
                Prims.op_Negation uu____2218 in
              if uu____2217
              then FStar_Tactics_Monad.fail "Codomain is effectful"
              else
                (let bv =
                   let uu____2231 = FStar_Tactics_Types.goal_type goal in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____2231 in
                 let bs =
                   let uu____2241 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2241; b] in
                 let env' =
                   let uu____2267 = FStar_Tactics_Types.goal_env goal in
                   FStar_TypeChecker_Env.push_binders uu____2267 bs in
                 let uu____2268 =
                   FStar_Tactics_Monad.new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c) in
                 FStar_Tactics_Monad.bind uu____2268
                   (fun uu____2293 ->
                      match uu____2293 with
                      | (u, ctx_uvar_u) ->
                          let lb =
                            let uu____2307 =
                              FStar_Tactics_Types.goal_type goal in
                            let uu____2310 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____2307
                              FStar_Parser_Const.effect_Tot_lid uu____2310 []
                              FStar_Range.dummyRange in
                          let body = FStar_Syntax_Syntax.bv_to_name bv in
                          let uu____2328 =
                            FStar_Syntax_Subst.close_let_rec [lb] body in
                          (match uu____2328 with
                           | (lbs, body1) ->
                               let tm =
                                 let uu____2350 =
                                   let uu____2351 =
                                     FStar_Tactics_Types.goal_witness goal in
                                   uu____2351.FStar_Syntax_Syntax.pos in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1)) uu____2350 in
                               let uu____2364 = set_solution goal tm in
                               FStar_Tactics_Monad.bind uu____2364
                                 (fun uu____2373 ->
                                    let uu____2374 =
                                      let uu____2377 =
                                        bnorm_goal
                                          (let uu___456_2380 = goal in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___456_2380.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___456_2380.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___456_2380.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___456_2380.FStar_Tactics_Types.label)
                                           }) in
                                      FStar_Tactics_Monad.replace_cur
                                        uu____2377 in
                                    FStar_Tactics_Monad.bind uu____2374
                                      (fun uu____2387 ->
                                         let uu____2388 =
                                           let uu____2393 =
                                             FStar_Syntax_Syntax.mk_binder bv in
                                           (uu____2393, b) in
                                         FStar_Tactics_Monad.ret uu____2388)))))
          | FStar_Pervasives_Native.None ->
              let uu____2402 =
                let uu____2403 = FStar_Tactics_Types.goal_env goal in
                let uu____2404 = FStar_Tactics_Types.goal_type goal in
                tts uu____2403 uu____2404 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2402))
let (norm :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____2426 ->
              let uu____2427 =
                let uu____2428 = FStar_Tactics_Types.goal_witness goal in
                FStar_Syntax_Print.term_to_string uu____2428 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2427)
           (fun uu____2433 ->
              let steps =
                let uu____2437 = FStar_TypeChecker_Normalize.tr_norm_steps s in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____2437 in
              let t =
                let uu____2441 = FStar_Tactics_Types.goal_env goal in
                let uu____2442 = FStar_Tactics_Types.goal_type goal in
                normalize steps uu____2441 uu____2442 in
              let uu____2443 = FStar_Tactics_Types.goal_with_type goal t in
              FStar_Tactics_Monad.replace_cur uu____2443))
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun s ->
      fun t ->
        let uu____2467 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____2475 -> g.FStar_Tactics_Types.opts
                 | uu____2478 -> FStar_Options.peek () in
               FStar_Tactics_Monad.mlog
                 (fun uu____2483 ->
                    let uu____2484 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____2484)
                 (fun uu____2487 ->
                    let uu____2488 = __tc_lax e t in
                    FStar_Tactics_Monad.bind uu____2488
                      (fun uu____2509 ->
                         match uu____2509 with
                         | (t1, uu____2519, uu____2520) ->
                             let steps =
                               let uu____2524 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____2524 in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1 in
                             FStar_Tactics_Monad.mlog
                               (fun uu____2530 ->
                                  let uu____2531 =
                                    FStar_Syntax_Print.term_to_string t2 in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____2531)
                               (fun uu____2533 -> FStar_Tactics_Monad.ret t2)))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_term")
          uu____2467
let (refine_intro : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____2544 ->
    let uu____2547 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____2554 =
             let uu____2565 = FStar_Tactics_Types.goal_env g in
             let uu____2566 = FStar_Tactics_Types.goal_type g in
             FStar_TypeChecker_Rel.base_and_refinement uu____2565 uu____2566 in
           match uu____2554 with
           | (uu____2569, FStar_Pervasives_Native.None) ->
               FStar_Tactics_Monad.fail "not a refinement"
           | (t, FStar_Pervasives_Native.Some (bv, phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t in
               let uu____2594 =
                 let uu____2599 =
                   let uu____2604 =
                     let uu____2605 = FStar_Syntax_Syntax.mk_binder bv in
                     [uu____2605] in
                   FStar_Syntax_Subst.open_term uu____2604 phi in
                 match uu____2599 with
                 | (bvs, phi1) ->
                     let uu____2630 =
                       let uu____2631 = FStar_List.hd bvs in
                       FStar_Pervasives_Native.fst uu____2631 in
                     (uu____2630, phi1) in
               (match uu____2594 with
                | (bv1, phi1) ->
                    let uu____2650 =
                      let uu____2653 = FStar_Tactics_Types.goal_env g in
                      let uu____2654 =
                        let uu____2655 =
                          let uu____2658 =
                            let uu____2659 =
                              let uu____2666 =
                                FStar_Tactics_Types.goal_witness g in
                              (bv1, uu____2666) in
                            FStar_Syntax_Syntax.NT uu____2659 in
                          [uu____2658] in
                        FStar_Syntax_Subst.subst uu____2655 phi1 in
                      FStar_Tactics_Monad.mk_irrelevant_goal
                        "refine_intro refinement" uu____2653 uu____2654
                        g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label in
                    FStar_Tactics_Monad.bind uu____2650
                      (fun g2 ->
                         FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                           (fun uu____2674 ->
                              FStar_Tactics_Monad.add_goals [g1; g2])))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "refine_intro")
      uu____2547
let (__exact_now :
  Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun set_expected_typ ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let env1 =
             if set_expected_typ
             then
               let uu____2698 = FStar_Tactics_Types.goal_env goal in
               let uu____2699 = FStar_Tactics_Types.goal_type goal in
               FStar_TypeChecker_Env.set_expected_typ uu____2698 uu____2699
             else FStar_Tactics_Types.goal_env goal in
           let uu____2701 = __tc env1 t in
           FStar_Tactics_Monad.bind uu____2701
             (fun uu____2720 ->
                match uu____2720 with
                | (t1, typ, guard) ->
                    FStar_Tactics_Monad.mlog
                      (fun uu____2735 ->
                         let uu____2736 =
                           FStar_Syntax_Print.term_to_string typ in
                         let uu____2737 =
                           let uu____2738 = FStar_Tactics_Types.goal_env goal in
                           FStar_TypeChecker_Rel.guard_to_string uu____2738
                             guard in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____2736 uu____2737)
                      (fun uu____2741 ->
                         let uu____2742 =
                           let uu____2745 = FStar_Tactics_Types.goal_env goal in
                           proc_guard "__exact typing" uu____2745 guard in
                         FStar_Tactics_Monad.bind uu____2742
                           (fun uu____2747 ->
                              FStar_Tactics_Monad.mlog
                                (fun uu____2751 ->
                                   let uu____2752 =
                                     FStar_Syntax_Print.term_to_string typ in
                                   let uu____2753 =
                                     let uu____2754 =
                                       FStar_Tactics_Types.goal_type goal in
                                     FStar_Syntax_Print.term_to_string
                                       uu____2754 in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____2752 uu____2753)
                                (fun uu____2757 ->
                                   let uu____2758 =
                                     let uu____2761 =
                                       FStar_Tactics_Types.goal_env goal in
                                     let uu____2762 =
                                       FStar_Tactics_Types.goal_type goal in
                                     do_unify uu____2761 typ uu____2762 in
                                   FStar_Tactics_Monad.bind uu____2758
                                     (fun b ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____2768 =
                                             let uu____2773 =
                                               let uu____2778 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal in
                                               tts uu____2778 in
                                             let uu____2779 =
                                               FStar_Tactics_Types.goal_type
                                                 goal in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu____2773 typ uu____2779 in
                                           match uu____2768 with
                                           | (typ1, goalt) ->
                                               let uu____2784 =
                                                 let uu____2785 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 tts uu____2785 t1 in
                                               let uu____2786 =
                                                 let uu____2787 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 let uu____2788 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal in
                                                 tts uu____2787 uu____2788 in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu____2784 typ1 goalt
                                                 uu____2786)))))))
let (t_exact :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun try_refine ->
    fun set_expected_typ ->
      fun tm ->
        let uu____2808 =
          FStar_Tactics_Monad.mlog
            (fun uu____2813 ->
               let uu____2814 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2814)
            (fun uu____2817 ->
               let uu____2818 =
                 let uu____2825 = __exact_now set_expected_typ tm in
                 catch uu____2825 in
               FStar_Tactics_Monad.bind uu____2818
                 (fun uu___2_2834 ->
                    match uu___2_2834 with
                    | FStar_Util.Inr r -> FStar_Tactics_Monad.ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        FStar_Tactics_Monad.traise e
                    | FStar_Util.Inl e ->
                        FStar_Tactics_Monad.mlog
                          (fun uu____2845 ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____2848 ->
                             let uu____2849 =
                               let uu____2856 =
                                 let uu____2859 =
                                   norm [FStar_Syntax_Embeddings.Delta] in
                                 FStar_Tactics_Monad.bind uu____2859
                                   (fun uu____2864 ->
                                      let uu____2865 = refine_intro () in
                                      FStar_Tactics_Monad.bind uu____2865
                                        (fun uu____2869 ->
                                           __exact_now set_expected_typ tm)) in
                               catch uu____2856 in
                             FStar_Tactics_Monad.bind uu____2849
                               (fun uu___1_2876 ->
                                  match uu___1_2876 with
                                  | FStar_Util.Inr r ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____2885 ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____2887 ->
                                           FStar_Tactics_Monad.ret ())
                                  | FStar_Util.Inl uu____2888 ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____2890 ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____2892 ->
                                           FStar_Tactics_Monad.traise e))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "exact") uu____2808
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
            let uu____2985 = f e ty2 ty1 in
            FStar_Tactics_Monad.bind uu____2985
              (fun uu___3_2997 ->
                 if uu___3_2997
                 then FStar_Tactics_Monad.ret acc
                 else
                   (let uu____3016 = FStar_Syntax_Util.arrow_one ty1 in
                    match uu____3016 with
                    | FStar_Pervasives_Native.None ->
                        let uu____3037 = term_to_string e ty1 in
                        let uu____3038 = term_to_string e ty2 in
                        fail2 "Could not instantiate, %s to %s" uu____3037
                          uu____3038
                    | FStar_Pervasives_Native.Some (b, c) ->
                        let uu____3053 =
                          let uu____3054 = FStar_Syntax_Util.is_total_comp c in
                          Prims.op_Negation uu____3054 in
                        if uu____3053
                        then FStar_Tactics_Monad.fail "Codomain is effectful"
                        else
                          (let uu____3074 =
                             FStar_Tactics_Monad.new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           FStar_Tactics_Monad.bind uu____3074
                             (fun uu____3098 ->
                                match uu____3098 with
                                | (uvt, uv) ->
                                    FStar_Tactics_Monad.mlog
                                      (fun uu____3125 ->
                                         let uu____3126 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             uv in
                                         FStar_Util.print1
                                           "t_apply: generated uvar %s\n"
                                           uu____3126)
                                      (fun uu____3130 ->
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
        let uu____3212 =
          FStar_Tactics_Monad.mlog
            (fun uu____3217 ->
               let uu____3218 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____3218)
            (fun uu____3220 ->
               FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                 (fun goal ->
                    let e = FStar_Tactics_Types.goal_env goal in
                    FStar_Tactics_Monad.mlog
                      (fun uu____3229 ->
                         let uu____3230 =
                           FStar_Syntax_Print.term_to_string tm in
                         let uu____3231 =
                           FStar_Tactics_Printing.goal_to_string_verbose goal in
                         let uu____3232 =
                           FStar_TypeChecker_Env.print_gamma
                             e.FStar_TypeChecker_Env.gamma in
                         FStar_Util.print3
                           "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\n"
                           uu____3230 uu____3231 uu____3232)
                      (fun uu____3235 ->
                         let uu____3236 = __tc e tm in
                         FStar_Tactics_Monad.bind uu____3236
                           (fun uu____3257 ->
                              match uu____3257 with
                              | (tm1, typ, guard) ->
                                  let typ1 = bnorm e typ in
                                  let uu____3270 =
                                    let uu____3281 =
                                      FStar_Tactics_Types.goal_type goal in
                                    try_unify_by_application only_match e
                                      typ1 uu____3281 in
                                  FStar_Tactics_Monad.bind uu____3270
                                    (fun uvs ->
                                       FStar_Tactics_Monad.mlog
                                         (fun uu____3302 ->
                                            let uu____3303 =
                                              FStar_Common.string_of_list
                                                (fun uu____3314 ->
                                                   match uu____3314 with
                                                   | (t, uu____3322,
                                                      uu____3323) ->
                                                       FStar_Syntax_Print.term_to_string
                                                         t) uvs in
                                            FStar_Util.print1
                                              "t_apply: found args = %s\n"
                                              uu____3303)
                                         (fun uu____3330 ->
                                            let fix_qual q =
                                              match q with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.Meta
                                                  uu____3345) ->
                                                  FStar_Pervasives_Native.Some
                                                    (FStar_Syntax_Syntax.Implicit
                                                       false)
                                              | uu____3346 -> q in
                                            let w =
                                              FStar_List.fold_right
                                                (fun uu____3369 ->
                                                   fun w ->
                                                     match uu____3369 with
                                                     | (uvt, q, uu____3387)
                                                         ->
                                                         FStar_Syntax_Util.mk_app
                                                           w
                                                           [(uvt,
                                                              (fix_qual q))])
                                                uvs tm1 in
                                            let uvset =
                                              let uu____3419 =
                                                FStar_Syntax_Free.new_uv_set
                                                  () in
                                              FStar_List.fold_right
                                                (fun uu____3436 ->
                                                   fun s ->
                                                     match uu____3436 with
                                                     | (uu____3448,
                                                        uu____3449, uv) ->
                                                         let uu____3451 =
                                                           FStar_Syntax_Free.uvars
                                                             uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                         FStar_Util.set_union
                                                           s uu____3451) uvs
                                                uu____3419 in
                                            let free_in_some_goal uv =
                                              FStar_Util.set_mem uv uvset in
                                            let uu____3460 = solve' goal w in
                                            FStar_Tactics_Monad.bind
                                              uu____3460
                                              (fun uu____3465 ->
                                                 let uu____3466 =
                                                   FStar_Tactics_Monad.mapM
                                                     (fun uu____3483 ->
                                                        match uu____3483 with
                                                        | (uvt, q, uv) ->
                                                            let uu____3495 =
                                                              FStar_Syntax_Unionfind.find
                                                                uv.FStar_Syntax_Syntax.ctx_uvar_head in
                                                            (match uu____3495
                                                             with
                                                             | FStar_Pervasives_Native.Some
                                                                 uu____3500
                                                                 ->
                                                                 FStar_Tactics_Monad.ret
                                                                   ()
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 let uu____3501
                                                                   =
                                                                   uopt &&
                                                                    (free_in_some_goal
                                                                    uv) in
                                                                 if
                                                                   uu____3501
                                                                 then
                                                                   FStar_Tactics_Monad.ret
                                                                    ()
                                                                 else
                                                                   (let uu____3505
                                                                    =
                                                                    let uu____3508
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___619_3511
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___619_3511.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___619_3511.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___619_3511.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    [uu____3508] in
                                                                    FStar_Tactics_Monad.add_goals
                                                                    uu____3505)))
                                                     uvs in
                                                 FStar_Tactics_Monad.bind
                                                   uu____3466
                                                   (fun uu____3515 ->
                                                      proc_guard
                                                        "apply guard" e guard)))))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply") uu____3212
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c in
    let uu____3540 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid in
    if uu____3540
    then
      let uu____3547 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3562 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3615 -> failwith "apply_lemma: impossible: not a lemma" in
      match uu____3547 with
      | (pre, post) ->
          let post1 =
            let uu____3647 =
              let uu____3658 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
              [uu____3658] in
            FStar_Syntax_Util.mk_app post uu____3647 in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____3688 =
         (FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)
           ||
           (FStar_Syntax_Util.is_ghost_effect
              ct.FStar_Syntax_Syntax.effect_name) in
       if uu____3688
       then
         let uu____3695 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ in
         FStar_Util.map_opt uu____3695
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
            let uu____3772 = f x e in
            FStar_Tactics_Monad.bind uu____3772
              (fun e' -> fold_left f e' xs1)
let (apply_lemma : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun tm ->
    let uu____3786 =
      let uu____3789 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps ->
             FStar_Tactics_Monad.mlog
               (fun uu____3796 ->
                  let uu____3797 = FStar_Syntax_Print.term_to_string tm in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3797)
               (fun uu____3800 ->
                  let is_unit_t t =
                    let uu____3807 =
                      let uu____3808 = FStar_Syntax_Subst.compress t in
                      uu____3808.FStar_Syntax_Syntax.n in
                    match uu____3807 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____3812 -> false in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                    (fun goal ->
                       let env1 = FStar_Tactics_Types.goal_env goal in
                       let uu____3818 = __tc env1 tm in
                       FStar_Tactics_Monad.bind uu____3818
                         (fun uu____3841 ->
                            match uu____3841 with
                            | (tm1, t, guard) ->
                                let uu____3853 =
                                  FStar_Syntax_Util.arrow_formals_comp t in
                                (match uu____3853 with
                                 | (bs, comp) ->
                                     let uu____3862 = lemma_or_sq comp in
                                     (match uu____3862 with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Tactics_Monad.fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre, post) ->
                                          let uu____3881 =
                                            fold_left
                                              (fun uu____3943 ->
                                                 fun uu____3944 ->
                                                   match (uu____3943,
                                                           uu____3944)
                                                   with
                                                   | ((b, aq),
                                                      (uvs, imps, subst)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst
                                                           b.FStar_Syntax_Syntax.sort in
                                                       let uu____4095 =
                                                         is_unit_t b_t in
                                                       if uu____4095
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
                                                         (let uu____4215 =
                                                            FStar_Tactics_Monad.new_uvar
                                                              "apply_lemma"
                                                              env1 b_t in
                                                          FStar_Tactics_Monad.bind
                                                            uu____4215
                                                            (fun uu____4251
                                                               ->
                                                               match uu____4251
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
                                          FStar_Tactics_Monad.bind uu____3881
                                            (fun uu____4438 ->
                                               match uu____4438 with
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
                                                   let uu____4527 =
                                                     let uu____4530 =
                                                       FStar_Syntax_Util.mk_squash
                                                         post_u post1 in
                                                     let uu____4531 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal in
                                                     do_unify env1 uu____4530
                                                       uu____4531 in
                                                   FStar_Tactics_Monad.bind
                                                     uu____4527
                                                     (fun b ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____4540 =
                                                            let uu____4545 =
                                                              FStar_Syntax_Util.mk_squash
                                                                post_u post1 in
                                                            let uu____4546 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal in
                                                            FStar_TypeChecker_Err.print_discrepancy
                                                              (tts env1)
                                                              uu____4545
                                                              uu____4546 in
                                                          match uu____4540
                                                          with
                                                          | (post2, goalt) ->
                                                              let uu____4551
                                                                =
                                                                tts env1 tm1 in
                                                              fail3
                                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                uu____4551
                                                                post2 goalt
                                                        else
                                                          (let uu____4553 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit in
                                                           FStar_Tactics_Monad.bind
                                                             uu____4553
                                                             (fun uu____4561
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____4588
                                                                    =
                                                                    let uu____4591
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1 in
                                                                    FStar_Util.set_elements
                                                                    uu____4591 in
                                                                    FStar_List.map
                                                                    (fun x ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____4588 in
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
                                                                    let uu____4628
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g' in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____4628)
                                                                    goals in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____4644
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1 in
                                                                  match uu____4644
                                                                  with
                                                                  | (hd,
                                                                    uu____4662)
                                                                    ->
                                                                    (match 
                                                                    hd.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,
                                                                    uu____4688)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____4705
                                                                    -> false) in
                                                                let uu____4706
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    implicits2
                                                                    (
                                                                    FStar_Tactics_Monad.mapM
                                                                    (fun imp
                                                                    ->
                                                                    let uu____4747
                                                                    = imp in
                                                                    match uu____4747
                                                                    with
                                                                    | 
                                                                    (term,
                                                                    ctx_uvar)
                                                                    ->
                                                                    let uu____4758
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____4758
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu____4780)
                                                                    ->
                                                                    let uu____4805
                                                                    =
                                                                    let uu____4806
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd in
                                                                    uu____4806.FStar_Syntax_Syntax.n in
                                                                    (match uu____4805
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,
                                                                    uu____4814)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___740_4834
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___740_4834.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___740_4834.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___740_4834.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___740_4834.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    FStar_Tactics_Monad.ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____4837
                                                                    ->
                                                                    FStar_Tactics_Monad.mlog
                                                                    (fun
                                                                    uu____4843
                                                                    ->
                                                                    let uu____4844
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                                                                    let uu____4845
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____4844
                                                                    uu____4845)
                                                                    (fun
                                                                    uu____4849
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env1
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                                    let uu____4851
                                                                    =
                                                                    let uu____4854
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____4855
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar in
                                                                    let uu____4856
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____4855
                                                                    uu____4856
                                                                    else
                                                                    "apply_lemma solved arg" in
                                                                    proc_guard
                                                                    uu____4854
                                                                    env1
                                                                    g_typ in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____4851
                                                                    (fun
                                                                    uu____4861
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    [])))))) in
                                                                FStar_Tactics_Monad.bind
                                                                  uu____4706
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
                                                                    let uu____4923
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____4923
                                                                    then
                                                                    let uu____4926
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____4926
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g ->
                                                                    fun goals
                                                                    ->
                                                                    let uu____4940
                                                                    =
                                                                    let uu____4941
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g in
                                                                    checkone
                                                                    uu____4941
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____4940)
                                                                    sub_goals1 in
                                                                    let uu____4942
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    env1
                                                                    guard in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____4942
                                                                    (fun
                                                                    uu____4948
                                                                    ->
                                                                    let pre_u
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 pre1 in
                                                                    let uu____4950
                                                                    =
                                                                    let uu____4953
                                                                    =
                                                                    let uu____4954
                                                                    =
                                                                    let uu____4955
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre_u
                                                                    pre1 in
                                                                    istrivial
                                                                    env1
                                                                    uu____4955 in
                                                                    Prims.op_Negation
                                                                    uu____4954 in
                                                                    if
                                                                    uu____4953
                                                                    then
                                                                    FStar_Tactics_Monad.add_irrelevant_goal
                                                                    goal
                                                                    "apply_lemma precondition"
                                                                    env1 pre1
                                                                    else
                                                                    FStar_Tactics_Monad.ret
                                                                    () in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____4950
                                                                    (fun
                                                                    uu____4960
                                                                    ->
                                                                    FStar_Tactics_Monad.add_goals
                                                                    sub_goals2))))))))))))) in
      focus uu____3789 in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply_lemma")
      uu____3786
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____4982 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____4982 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,
         uu____4992::(e1, FStar_Pervasives_Native.None)::(e2,
                                                          FStar_Pervasives_Native.None)::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l, uu____5052::uu____5053::(e1, uu____5055)::(e2, uu____5057)::[]))
        when FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5134 ->
        let uu____5137 = FStar_Syntax_Util.unb2t typ in
        (match uu____5137 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____5151 = FStar_Syntax_Util.head_and_args t in
             (match uu____5151 with
              | (hd, args) ->
                  let uu____5200 =
                    let uu____5215 =
                      let uu____5216 = FStar_Syntax_Subst.compress hd in
                      uu____5216.FStar_Syntax_Syntax.n in
                    (uu____5215, args) in
                  (match uu____5200 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,
                      (uu____5236, FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____5237))::(e1,
                                                                    FStar_Pervasives_Native.None)::
                      (e2, FStar_Pervasives_Native.None)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____5304 -> FStar_Pervasives_Native.None)))
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____5340 = destruct_eq' typ in
    match uu____5340 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None ->
        let uu____5370 = FStar_Syntax_Util.un_squash typ in
        (match uu____5370 with
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
        let uu____5438 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____5438 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv', e') ->
            let uu____5473 = FStar_Syntax_Syntax.bv_eq bvar bv' in
            if uu____5473
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____5495 = aux e' in
               FStar_Util.map_opt uu____5495
                 (fun uu____5526 ->
                    match uu____5526 with
                    | (e'', bv, bvs) -> (e'', bv, (bv' :: bvs)))) in
      let uu____5552 = aux e in
      FStar_Util.map_opt uu____5552
        (fun uu____5583 ->
           match uu____5583 with
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
        let uu____5658 =
          let uu____5669 = FStar_Tactics_Types.goal_env g in
          split_env b1 uu____5669 in
        match uu____5658 with
        | FStar_Pervasives_Native.Some (e0, b11, bvs) ->
            let bs =
              FStar_List.map FStar_Syntax_Syntax.mk_binder (b11 :: bvs) in
            let t = FStar_Tactics_Types.goal_type g in
            let uu____5709 =
              let uu____5722 = FStar_Syntax_Subst.close_binders bs in
              let uu____5731 = FStar_Syntax_Subst.close bs t in
              (uu____5722, uu____5731) in
            (match uu____5709 with
             | (bs', t') ->
                 let bs'1 =
                   let uu____5775 = FStar_Syntax_Syntax.mk_binder b2 in
                   let uu____5782 = FStar_List.tail bs' in uu____5775 ::
                     uu____5782 in
                 let uu____5803 = FStar_Syntax_Subst.open_term bs'1 t' in
                 (match uu____5803 with
                  | (bs'', t'') ->
                      let b21 =
                        let uu____5819 = FStar_List.hd bs'' in
                        FStar_Pervasives_Native.fst uu____5819 in
                      let new_env =
                        let uu____5835 =
                          FStar_List.map FStar_Pervasives_Native.fst bs'' in
                        push_bvs e0 uu____5835 in
                      let uu____5846 =
                        FStar_Tactics_Monad.new_uvar "subst_goal" new_env t'' in
                      FStar_Tactics_Monad.bind uu____5846
                        (fun uu____5869 ->
                           match uu____5869 with
                           | (uvt, uv) ->
                               let goal' =
                                 FStar_Tactics_Types.mk_goal new_env uv
                                   g.FStar_Tactics_Types.opts
                                   g.FStar_Tactics_Types.is_guard
                                   g.FStar_Tactics_Types.label in
                               let sol =
                                 let uu____5888 =
                                   FStar_Syntax_Util.abs bs'' uvt
                                     FStar_Pervasives_Native.None in
                                 let uu____5891 =
                                   FStar_List.map
                                     (fun uu____5912 ->
                                        match uu____5912 with
                                        | (bv, q) ->
                                            let uu____5925 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                bv in
                                            FStar_Syntax_Syntax.as_arg
                                              uu____5925) bs in
                                 FStar_Syntax_Util.mk_app uu____5888
                                   uu____5891 in
                               let uu____5926 = set_solution g sol in
                               FStar_Tactics_Monad.bind uu____5926
                                 (fun uu____5936 ->
                                    FStar_Tactics_Monad.ret
                                      (FStar_Pervasives_Native.Some
                                         (b21, goal'))))))
        | FStar_Pervasives_Native.None ->
            FStar_Tactics_Monad.ret FStar_Pervasives_Native.None
let (rewrite : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun h ->
    let uu____5974 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____5982 = h in
           match uu____5982 with
           | (bv, uu____5986) ->
               FStar_Tactics_Monad.mlog
                 (fun uu____5994 ->
                    let uu____5995 = FStar_Syntax_Print.bv_to_string bv in
                    let uu____5996 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5995
                      uu____5996)
                 (fun uu____5999 ->
                    let uu____6000 =
                      let uu____6011 = FStar_Tactics_Types.goal_env goal in
                      split_env bv uu____6011 in
                    match uu____6000 with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.fail
                          "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                        let uu____6037 =
                          let uu____6044 =
                            whnf e0 bv1.FStar_Syntax_Syntax.sort in
                          destruct_eq uu____6044 in
                        (match uu____6037 with
                         | FStar_Pervasives_Native.Some (x, e) ->
                             let uu____6053 =
                               let uu____6054 = FStar_Syntax_Subst.compress x in
                               uu____6054.FStar_Syntax_Syntax.n in
                             (match uu____6053 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                  let t = FStar_Tactics_Types.goal_type goal in
                                  let bs =
                                    FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder bvs in
                                  let uu____6081 =
                                    let uu____6086 =
                                      FStar_Syntax_Subst.close_binders bs in
                                    let uu____6087 =
                                      FStar_Syntax_Subst.close bs t in
                                    (uu____6086, uu____6087) in
                                  (match uu____6081 with
                                   | (bs', t') ->
                                       let uu____6092 =
                                         let uu____6097 =
                                           FStar_Syntax_Subst.subst_binders s
                                             bs' in
                                         let uu____6098 =
                                           FStar_Syntax_Subst.subst s t in
                                         (uu____6097, uu____6098) in
                                       (match uu____6092 with
                                        | (bs'1, t'1) ->
                                            let uu____6103 =
                                              FStar_Syntax_Subst.open_term
                                                bs'1 t'1 in
                                            (match uu____6103 with
                                             | (bs'', t'') ->
                                                 let new_env =
                                                   let uu____6113 =
                                                     let uu____6116 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         bs'' in
                                                     bv1 :: uu____6116 in
                                                   push_bvs e0 uu____6113 in
                                                 let uu____6127 =
                                                   FStar_Tactics_Monad.new_uvar
                                                     "rewrite" new_env t'' in
                                                 FStar_Tactics_Monad.bind
                                                   uu____6127
                                                   (fun uu____6144 ->
                                                      match uu____6144 with
                                                      | (uvt, uv) ->
                                                          let goal' =
                                                            FStar_Tactics_Types.mk_goal
                                                              new_env uv
                                                              goal.FStar_Tactics_Types.opts
                                                              goal.FStar_Tactics_Types.is_guard
                                                              goal.FStar_Tactics_Types.label in
                                                          let sol =
                                                            let uu____6157 =
                                                              FStar_Syntax_Util.abs
                                                                bs'' uvt
                                                                FStar_Pervasives_Native.None in
                                                            let uu____6160 =
                                                              FStar_List.map
                                                                (fun
                                                                   uu____6181
                                                                   ->
                                                                   match uu____6181
                                                                   with
                                                                   | 
                                                                   (bv2,
                                                                    uu____6189)
                                                                    ->
                                                                    let uu____6194
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv2 in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____6194)
                                                                bs in
                                                            FStar_Syntax_Util.mk_app
                                                              uu____6157
                                                              uu____6160 in
                                                          let uu____6195 =
                                                            set_solution goal
                                                              sol in
                                                          FStar_Tactics_Monad.bind
                                                            uu____6195
                                                            (fun uu____6199
                                                               ->
                                                               FStar_Tactics_Monad.replace_cur
                                                                 goal')))))
                              | uu____6200 ->
                                  FStar_Tactics_Monad.fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6201 ->
                             FStar_Tactics_Monad.fail
                               "Not an equality hypothesis"))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rewrite") uu____5974
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac)
  =
  fun b ->
    fun s ->
      let uu____6226 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____6248 = b in
             match uu____6248 with
             | (bv, q) ->
                 let bv' =
                   let uu____6264 =
                     let uu___918_6265 = bv in
                     let uu____6266 =
                       let uu____6267 =
                         let uu____6272 =
                           FStar_Ident.range_of_id
                             bv.FStar_Syntax_Syntax.ppname in
                         (s, uu____6272) in
                       FStar_Ident.mk_ident uu____6267 in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6266;
                       FStar_Syntax_Syntax.index =
                         (uu___918_6265.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___918_6265.FStar_Syntax_Syntax.sort)
                     } in
                   FStar_Syntax_Syntax.freshen_bv uu____6264 in
                 let uu____6273 = subst_goal bv bv' goal in
                 FStar_Tactics_Monad.bind uu____6273
                   (fun uu___4_6295 ->
                      match uu___4_6295 with
                      | FStar_Pervasives_Native.None ->
                          FStar_Tactics_Monad.fail
                            "binder not found in environment"
                      | FStar_Pervasives_Native.Some (bv'1, goal1) ->
                          let uu____6326 =
                            FStar_Tactics_Monad.replace_cur goal1 in
                          FStar_Tactics_Monad.bind uu____6326
                            (fun uu____6336 ->
                               FStar_Tactics_Monad.ret (bv'1, q)))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rename_to")
        uu____6226
let (binder_retype :
  FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let uu____6370 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____6379 = b in
           match uu____6379 with
           | (bv, uu____6383) ->
               let uu____6388 =
                 let uu____6399 = FStar_Tactics_Types.goal_env goal in
                 split_env bv uu____6399 in
               (match uu____6388 with
                | FStar_Pervasives_Native.None ->
                    FStar_Tactics_Monad.fail
                      "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                    let uu____6425 = FStar_Syntax_Util.type_u () in
                    (match uu____6425 with
                     | (ty, u) ->
                         let uu____6434 =
                           FStar_Tactics_Monad.new_uvar "binder_retype" e0 ty in
                         FStar_Tactics_Monad.bind uu____6434
                           (fun uu____6452 ->
                              match uu____6452 with
                              | (t', u_t') ->
                                  let bv'' =
                                    let uu___945_6462 = bv1 in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___945_6462.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___945_6462.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    } in
                                  let s =
                                    let uu____6466 =
                                      let uu____6467 =
                                        let uu____6474 =
                                          FStar_Syntax_Syntax.bv_to_name bv'' in
                                        (bv1, uu____6474) in
                                      FStar_Syntax_Syntax.NT uu____6467 in
                                    [uu____6466] in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1 ->
                                         let uu___950_6486 = b1 in
                                         let uu____6487 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___950_6486.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___950_6486.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6487
                                         }) bvs in
                                  let env' = push_bvs e0 (bv'' :: bvs1) in
                                  FStar_Tactics_Monad.bind
                                    FStar_Tactics_Monad.dismiss
                                    (fun uu____6494 ->
                                       let new_goal =
                                         let uu____6496 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env' in
                                         let uu____6497 =
                                           let uu____6498 =
                                             FStar_Tactics_Types.goal_type
                                               goal in
                                           FStar_Syntax_Subst.subst s
                                             uu____6498 in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6496 uu____6497 in
                                       let uu____6499 =
                                         FStar_Tactics_Monad.add_goals
                                           [new_goal] in
                                       FStar_Tactics_Monad.bind uu____6499
                                         (fun uu____6504 ->
                                            let uu____6505 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t' in
                                            FStar_Tactics_Monad.add_irrelevant_goal
                                              goal "binder_retype equation"
                                              e0 uu____6505)))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "binder_retype")
      uu____6370
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    fun b ->
      let uu____6528 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____6537 = b in
             match uu____6537 with
             | (bv, uu____6541) ->
                 let uu____6546 =
                   let uu____6557 = FStar_Tactics_Types.goal_env goal in
                   split_env bv uu____6557 in
                 (match uu____6546 with
                  | FStar_Pervasives_Native.None ->
                      FStar_Tactics_Monad.fail
                        "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                      let steps =
                        let uu____6586 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6586 in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort in
                      let bv' =
                        let uu___971_6591 = bv1 in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___971_6591.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___971_6591.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        } in
                      let env' = push_bvs e0 (bv' :: bvs) in
                      let uu____6593 =
                        FStar_Tactics_Types.goal_with_env goal env' in
                      FStar_Tactics_Monad.replace_cur uu____6593)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_binder_type")
        uu____6528
let (revert : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____6604 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____6610 =
           let uu____6617 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____6617 in
         match uu____6610 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x, env') ->
             let typ' =
               let uu____6633 =
                 let uu____6636 = FStar_Tactics_Types.goal_type goal in
                 FStar_Syntax_Syntax.mk_Total uu____6636 in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6633 in
             let uu____6651 = FStar_Tactics_Monad.new_uvar "revert" env' typ' in
             FStar_Tactics_Monad.bind uu____6651
               (fun uu____6666 ->
                  match uu____6666 with
                  | (r, u_r) ->
                      let uu____6675 =
                        let uu____6678 =
                          let uu____6679 =
                            let uu____6680 =
                              let uu____6689 =
                                FStar_Syntax_Syntax.bv_to_name x in
                              FStar_Syntax_Syntax.as_arg uu____6689 in
                            [uu____6680] in
                          let uu____6706 =
                            let uu____6707 =
                              FStar_Tactics_Types.goal_type goal in
                            uu____6707.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.mk_Tm_app r uu____6679
                            uu____6706 in
                        set_solution goal uu____6678 in
                      FStar_Tactics_Monad.bind uu____6675
                        (fun uu____6712 ->
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
      let uu____6724 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____6724
let (clear : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let bv = FStar_Pervasives_Native.fst b in
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____6744 ->
              let uu____6745 = FStar_Syntax_Print.binder_to_string b in
              let uu____6746 =
                let uu____6747 =
                  let uu____6748 =
                    let uu____6757 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.all_binders uu____6757 in
                  FStar_All.pipe_right uu____6748 FStar_List.length in
                FStar_All.pipe_right uu____6747 FStar_Util.string_of_int in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6745 uu____6746)
           (fun uu____6774 ->
              let uu____6775 =
                let uu____6786 = FStar_Tactics_Types.goal_env goal in
                split_env bv uu____6786 in
              match uu____6775 with
              | FStar_Pervasives_Native.None ->
                  FStar_Tactics_Monad.fail
                    "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e', bv1, bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> FStar_Tactics_Monad.ret ()
                    | bv'::bvs2 ->
                        let uu____6830 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort in
                        if uu____6830
                        then
                          let uu____6833 =
                            let uu____6834 =
                              FStar_Syntax_Print.bv_to_string bv' in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6834 in
                          FStar_Tactics_Monad.fail uu____6833
                        else check bvs2 in
                  let uu____6836 =
                    let uu____6837 = FStar_Tactics_Types.goal_type goal in
                    free_in bv1 uu____6837 in
                  if uu____6836
                  then
                    FStar_Tactics_Monad.fail
                      "Cannot clear; binder present in goal"
                  else
                    (let uu____6841 = check bvs in
                     FStar_Tactics_Monad.bind uu____6841
                       (fun uu____6847 ->
                          let env' = push_bvs e' bvs in
                          let uu____6849 =
                            let uu____6856 =
                              FStar_Tactics_Types.goal_type goal in
                            FStar_Tactics_Monad.new_uvar "clear.witness" env'
                              uu____6856 in
                          FStar_Tactics_Monad.bind uu____6849
                            (fun uu____6865 ->
                               match uu____6865 with
                               | (ut, uvar_ut) ->
                                   let uu____6874 = set_solution goal ut in
                                   FStar_Tactics_Monad.bind uu____6874
                                     (fun uu____6879 ->
                                        let uu____6880 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label in
                                        FStar_Tactics_Monad.replace_cur
                                          uu____6880))))))
let (clear_top : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____6887 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____6893 =
           let uu____6900 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____6900 in
         match uu____6893 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x, uu____6908) ->
             let uu____6913 = FStar_Syntax_Syntax.mk_binder x in
             clear uu____6913)
let (prune : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____6930 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6930 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (addns : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____6948 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6948 in
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
           let uu____6967 =
             let uu____6970 = FStar_Tactics_Types.goal_env g in
             do_unify uu____6970 l r in
           FStar_Tactics_Monad.bind uu____6967
             (fun b ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____6977 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____6977 l in
                   let r1 =
                     let uu____6979 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____6979 r in
                   let uu____6980 =
                     let uu____6983 = FStar_Tactics_Types.goal_env g in
                     do_unify uu____6983 l1 r1 in
                   FStar_Tactics_Monad.bind uu____6980
                     (fun b1 ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____6989 =
                             let uu____6994 =
                               let uu____6999 =
                                 FStar_Tactics_Types.goal_env g in
                               tts uu____6999 in
                             FStar_TypeChecker_Err.print_discrepancy
                               uu____6994 l1 r1 in
                           match uu____6989 with
                           | (ls, rs) ->
                               fail2 "not a trivial equality ((%s) vs (%s))"
                                 ls rs)))))
let (trefl : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7010 ->
    let uu____7013 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____7021 =
             let uu____7028 =
               let uu____7029 = FStar_Tactics_Types.goal_env g in
               let uu____7030 = FStar_Tactics_Types.goal_type g in
               whnf uu____7029 uu____7030 in
             destruct_eq uu____7028 in
           match uu____7021 with
           | FStar_Pervasives_Native.Some (l, r) -> _trefl l r
           | FStar_Pervasives_Native.None ->
               let uu____7043 =
                 let uu____7044 = FStar_Tactics_Types.goal_env g in
                 let uu____7045 = FStar_Tactics_Types.goal_type g in
                 tts uu____7044 uu____7045 in
               fail1 "not an equality (%s)" uu____7043) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "trefl") uu____7013
let (dup : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7056 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let env1 = FStar_Tactics_Types.goal_env g in
         let uu____7064 =
           let uu____7071 = FStar_Tactics_Types.goal_type g in
           FStar_Tactics_Monad.new_uvar "dup" env1 uu____7071 in
         FStar_Tactics_Monad.bind uu____7064
           (fun uu____7080 ->
              match uu____7080 with
              | (u, u_uvar) ->
                  let g' =
                    let uu___1057_7090 = g in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1057_7090.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1057_7090.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1057_7090.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1057_7090.FStar_Tactics_Types.label)
                    } in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____7094 ->
                       let t_eq =
                         let uu____7096 =
                           let uu____7097 = FStar_Tactics_Types.goal_type g in
                           env1.FStar_TypeChecker_Env.universe_of env1
                             uu____7097 in
                         let uu____7098 = FStar_Tactics_Types.goal_type g in
                         let uu____7099 = FStar_Tactics_Types.goal_witness g in
                         FStar_Syntax_Util.mk_eq2 uu____7096 uu____7098 u
                           uu____7099 in
                       let uu____7100 =
                         FStar_Tactics_Monad.add_irrelevant_goal g
                           "dup equation" env1 t_eq in
                       FStar_Tactics_Monad.bind uu____7100
                         (fun uu____7105 ->
                            let uu____7106 =
                              FStar_Tactics_Monad.add_goals [g'] in
                            FStar_Tactics_Monad.bind uu____7106
                              (fun uu____7110 -> FStar_Tactics_Monad.ret ())))))
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
              let uu____7233 = f x y in
              if uu____7233 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____7253 -> (acc, l11, l21) in
        let uu____7268 = aux [] l1 l2 in
        match uu____7268 with | (pr, t1, t2) -> ((FStar_List.rev pr), t1, t2)
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
      let uu____7373 = FStar_Tactics_Types.get_phi g1 in
      match uu____7373 with
      | FStar_Pervasives_Native.None ->
          FStar_Tactics_Monad.fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____7379 = FStar_Tactics_Types.get_phi g2 in
          (match uu____7379 with
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let uu____7391 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2) in
               (match uu____7391 with
                | (gamma, r1, r2) ->
                    let t1 =
                      let uu____7422 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1) in
                      close_forall_no_univs uu____7422 phi1 in
                    let t2 =
                      let uu____7432 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2) in
                      close_forall_no_univs uu____7432 phi2 in
                    let uu____7441 =
                      set_solution g1 FStar_Syntax_Util.exp_unit in
                    FStar_Tactics_Monad.bind uu____7441
                      (fun uu____7446 ->
                         let uu____7447 =
                           set_solution g2 FStar_Syntax_Util.exp_unit in
                         FStar_Tactics_Monad.bind uu____7447
                           (fun uu____7454 ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2 in
                              let nenv =
                                let uu___1109_7459 =
                                  FStar_Tactics_Types.goal_env g1 in
                                let uu____7460 =
                                  FStar_Util.smap_create (Prims.of_int (100)) in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1109_7459.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1109_7459.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1109_7459.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1109_7459.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____7460;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1109_7459.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1109_7459.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1109_7459.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1109_7459.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1109_7459.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1109_7459.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1109_7459.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1109_7459.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1109_7459.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1109_7459.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1109_7459.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1109_7459.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1109_7459.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1109_7459.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1109_7459.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1109_7459.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1109_7459.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1109_7459.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1109_7459.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1109_7459.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1109_7459.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1109_7459.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1109_7459.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1109_7459.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1109_7459.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1109_7459.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1109_7459.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1109_7459.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1109_7459.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1109_7459.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1109_7459.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1109_7459.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1109_7459.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1109_7459.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1109_7459.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1109_7459.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1109_7459.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1109_7459.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1109_7459.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1109_7459.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___1109_7459.FStar_TypeChecker_Env.enable_defer_to_tac)
                                } in
                              let uu____7463 =
                                FStar_Tactics_Monad.mk_irrelevant_goal
                                  "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label in
                              FStar_Tactics_Monad.bind uu____7463
                                (fun goal ->
                                   FStar_Tactics_Monad.mlog
                                     (fun uu____7472 ->
                                        let uu____7473 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g1 in
                                        let uu____7474 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g2 in
                                        let uu____7475 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            goal in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____7473 uu____7474 uu____7475)
                                     (fun uu____7477 ->
                                        FStar_Tactics_Monad.ret goal))))))
let (join : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7484 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____7500 =
               FStar_Tactics_Monad.set
                 (let uu___1124_7505 = ps in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1124_7505.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1124_7505.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1124_7505.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1124_7505.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1124_7505.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1124_7505.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1124_7505.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1124_7505.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1124_7505.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1124_7505.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1124_7505.FStar_Tactics_Types.local_state)
                  }) in
             FStar_Tactics_Monad.bind uu____7500
               (fun uu____7508 ->
                  let uu____7509 = join_goals g1 g2 in
                  FStar_Tactics_Monad.bind uu____7509
                    (fun g12 -> FStar_Tactics_Monad.add_goals [g12]))
         | uu____7514 -> FStar_Tactics_Monad.fail "join: less than 2 goals")
let (set_options : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    let uu____7526 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           FStar_Options.push ();
           (let uu____7539 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
            FStar_Options.set uu____7539);
           (let res = FStar_Options.set_options s in
            let opts' = FStar_Options.peek () in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success ->
                 let g' =
                   let uu___1135_7546 = g in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1135_7546.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1135_7546.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1135_7546.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1135_7546.FStar_Tactics_Types.label)
                   } in
                 FStar_Tactics_Monad.replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "set_options")
      uu____7526
let (top_env : unit -> env FStar_Tactics_Monad.tac) =
  fun uu____7558 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_All.pipe_left FStar_Tactics_Monad.ret
           ps.FStar_Tactics_Types.main_context)
let (lax_on : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____7571 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let uu____7577 =
           (FStar_Options.lax ()) ||
             (let uu____7579 = FStar_Tactics_Types.goal_env g in
              uu____7579.FStar_TypeChecker_Env.lax) in
         FStar_Tactics_Monad.ret uu____7577)
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun tm ->
      let uu____7594 =
        FStar_Tactics_Monad.mlog
          (fun uu____7599 ->
             let uu____7600 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "unquote: tm = %s\n" uu____7600)
          (fun uu____7602 ->
             FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
               (fun goal ->
                  let env1 =
                    let uu____7608 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.set_expected_typ uu____7608 ty in
                  let uu____7609 = __tc_ghost env1 tm in
                  FStar_Tactics_Monad.bind uu____7609
                    (fun uu____7628 ->
                       match uu____7628 with
                       | (tm1, typ, guard) ->
                           FStar_Tactics_Monad.mlog
                             (fun uu____7642 ->
                                let uu____7643 =
                                  FStar_Syntax_Print.term_to_string tm1 in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____7643)
                             (fun uu____7645 ->
                                FStar_Tactics_Monad.mlog
                                  (fun uu____7648 ->
                                     let uu____7649 =
                                       FStar_Syntax_Print.term_to_string typ in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____7649)
                                  (fun uu____7652 ->
                                     let uu____7653 =
                                       proc_guard "unquote" env1 guard in
                                     FStar_Tactics_Monad.bind uu____7653
                                       (fun uu____7657 ->
                                          FStar_Tactics_Monad.ret tm1)))))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unquote") uu____7594
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun ty ->
      let uu____7680 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> FStar_Tactics_Monad.ret ty1
        | FStar_Pervasives_Native.None ->
            let uu____7686 =
              let uu____7693 =
                let uu____7694 = FStar_Syntax_Util.type_u () in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7694 in
              FStar_Tactics_Monad.new_uvar "uvar_env.2" env1 uu____7693 in
            FStar_Tactics_Monad.bind uu____7686
              (fun uu____7710 ->
                 match uu____7710 with
                 | (typ, uvar_typ) -> FStar_Tactics_Monad.ret typ) in
      FStar_Tactics_Monad.bind uu____7680
        (fun typ ->
           let uu____7722 = FStar_Tactics_Monad.new_uvar "uvar_env" env1 typ in
           FStar_Tactics_Monad.bind uu____7722
             (fun uu____7736 ->
                match uu____7736 with
                | (t, uvar_t) -> FStar_Tactics_Monad.ret t))
let (unshelve : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____7754 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           let env1 = ps.FStar_Tactics_Types.main_context in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____7773 -> g.FStar_Tactics_Types.opts
             | uu____7776 -> FStar_Options.peek () in
           let uu____7779 = FStar_Syntax_Util.head_and_args t in
           match uu____7779 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar, uu____7799);
                FStar_Syntax_Syntax.pos = uu____7800;
                FStar_Syntax_Syntax.vars = uu____7801;_},
              uu____7802) ->
               let env2 =
                 let uu___1189_7844 = env1 in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1189_7844.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1189_7844.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1189_7844.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1189_7844.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1189_7844.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1189_7844.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1189_7844.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1189_7844.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1189_7844.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1189_7844.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1189_7844.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1189_7844.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1189_7844.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1189_7844.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1189_7844.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1189_7844.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___1189_7844.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1189_7844.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1189_7844.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1189_7844.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1189_7844.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1189_7844.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1189_7844.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1189_7844.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1189_7844.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1189_7844.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1189_7844.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1189_7844.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1189_7844.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1189_7844.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1189_7844.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1189_7844.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1189_7844.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1189_7844.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1189_7844.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___1189_7844.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1189_7844.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1189_7844.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1189_7844.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1189_7844.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1189_7844.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1189_7844.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1189_7844.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1189_7844.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1189_7844.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (uu___1189_7844.FStar_TypeChecker_Env.enable_defer_to_tac)
                 } in
               let g =
                 FStar_Tactics_Types.mk_goal env2 ctx_uvar opts false "" in
               let uu____7846 = let uu____7849 = bnorm_goal g in [uu____7849] in
               FStar_Tactics_Monad.add_goals uu____7846
           | uu____7850 -> FStar_Tactics_Monad.fail "not a uvar") in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unshelve") uu____7754
let (tac_and :
  Prims.bool FStar_Tactics_Monad.tac ->
    Prims.bool FStar_Tactics_Monad.tac -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let comp =
        FStar_Tactics_Monad.bind t1
          (fun b ->
             let uu____7899 = if b then t2 else FStar_Tactics_Monad.ret false in
             FStar_Tactics_Monad.bind uu____7899
               (fun b' ->
                  if b'
                  then FStar_Tactics_Monad.ret b'
                  else FStar_Tactics_Monad.fail "")) in
      let uu____7910 = trytac comp in
      FStar_Tactics_Monad.bind uu____7910
        (fun uu___5_7918 ->
           match uu___5_7918 with
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
        let uu____7944 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu____7950 = __tc e t1 in
               FStar_Tactics_Monad.bind uu____7950
                 (fun uu____7970 ->
                    match uu____7970 with
                    | (t11, ty1, g1) ->
                        let uu____7982 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu____7982
                          (fun uu____8002 ->
                             match uu____8002 with
                             | (t21, ty2, g2) ->
                                 let uu____8014 =
                                   proc_guard "unify_env g1" e g1 in
                                 FStar_Tactics_Monad.bind uu____8014
                                   (fun uu____8019 ->
                                      let uu____8020 =
                                        proc_guard "unify_env g2" e g2 in
                                      FStar_Tactics_Monad.bind uu____8020
                                        (fun uu____8026 ->
                                           let uu____8027 =
                                             do_unify e ty1 ty2 in
                                           let uu____8030 =
                                             do_unify e t11 t21 in
                                           tac_and uu____8027 uu____8030))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unify_env")
          uu____7944
let (launch_process :
  Prims.string ->
    Prims.string Prims.list ->
      Prims.string -> Prims.string FStar_Tactics_Monad.tac)
  =
  fun prog ->
    fun args ->
      fun input ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____8063 ->
             let uu____8064 = FStar_Options.unsafe_tactic_exec () in
             if uu____8064
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
        (fun uu____8085 ->
           let uu____8086 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t in
           FStar_Tactics_Monad.ret uu____8086)
let (change : FStar_Reflection_Data.typ -> unit FStar_Tactics_Monad.tac) =
  fun ty ->
    let uu____8096 =
      FStar_Tactics_Monad.mlog
        (fun uu____8101 ->
           let uu____8102 = FStar_Syntax_Print.term_to_string ty in
           FStar_Util.print1 "change: ty = %s\n" uu____8102)
        (fun uu____8104 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                let uu____8108 =
                  let uu____8117 = FStar_Tactics_Types.goal_env g in
                  __tc uu____8117 ty in
                FStar_Tactics_Monad.bind uu____8108
                  (fun uu____8129 ->
                     match uu____8129 with
                     | (ty1, uu____8139, guard) ->
                         let uu____8141 =
                           let uu____8144 = FStar_Tactics_Types.goal_env g in
                           proc_guard "change" uu____8144 guard in
                         FStar_Tactics_Monad.bind uu____8141
                           (fun uu____8147 ->
                              let uu____8148 =
                                let uu____8151 =
                                  FStar_Tactics_Types.goal_env g in
                                let uu____8152 =
                                  FStar_Tactics_Types.goal_type g in
                                do_unify uu____8151 uu____8152 ty1 in
                              FStar_Tactics_Monad.bind uu____8148
                                (fun bb ->
                                   if bb
                                   then
                                     let uu____8158 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1 in
                                     FStar_Tactics_Monad.replace_cur
                                       uu____8158
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops] in
                                      let ng =
                                        let uu____8164 =
                                          FStar_Tactics_Types.goal_env g in
                                        let uu____8165 =
                                          FStar_Tactics_Types.goal_type g in
                                        normalize steps uu____8164 uu____8165 in
                                      let nty =
                                        let uu____8167 =
                                          FStar_Tactics_Types.goal_env g in
                                        normalize steps uu____8167 ty1 in
                                      let uu____8168 =
                                        let uu____8171 =
                                          FStar_Tactics_Types.goal_env g in
                                        do_unify uu____8171 ng nty in
                                      FStar_Tactics_Monad.bind uu____8168
                                        (fun b ->
                                           if b
                                           then
                                             let uu____8177 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1 in
                                             FStar_Tactics_Monad.replace_cur
                                               uu____8177
                                           else
                                             FStar_Tactics_Monad.fail
                                               "not convertible"))))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "change") uu____8096
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
    let uu____8240 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____8258 =
             let uu____8267 = FStar_Tactics_Types.goal_env g in
             __tc uu____8267 s_tm in
           FStar_Tactics_Monad.bind uu____8258
             (fun uu____8285 ->
                match uu____8285 with
                | (s_tm1, s_ty, guard) ->
                    let uu____8303 =
                      let uu____8306 = FStar_Tactics_Types.goal_env g in
                      proc_guard "destruct" uu____8306 guard in
                    FStar_Tactics_Monad.bind uu____8303
                      (fun uu____8319 ->
                         let s_ty1 =
                           let uu____8321 = FStar_Tactics_Types.goal_env g in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant] uu____8321
                             s_ty in
                         let uu____8322 =
                           let uu____8337 = FStar_Syntax_Util.unrefine s_ty1 in
                           FStar_Syntax_Util.head_and_args' uu____8337 in
                         match uu____8322 with
                         | (h, args) ->
                             let uu____8368 =
                               let uu____8375 =
                                 let uu____8376 =
                                   FStar_Syntax_Subst.compress h in
                                 uu____8376.FStar_Syntax_Syntax.n in
                               match uu____8375 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   FStar_Tactics_Monad.ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____8391;
                                      FStar_Syntax_Syntax.vars = uu____8392;_},
                                    us)
                                   -> FStar_Tactics_Monad.ret (fv, us)
                               | uu____8402 ->
                                   FStar_Tactics_Monad.fail
                                     "type is not an fv" in
                             FStar_Tactics_Monad.bind uu____8368
                               (fun uu____8422 ->
                                  match uu____8422 with
                                  | (fv, a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv in
                                      let uu____8438 =
                                        let uu____8441 =
                                          FStar_Tactics_Types.goal_env g in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____8441 t_lid in
                                      (match uu____8438 with
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
                                                let uu____8480 =
                                                  erasable &&
                                                    (let uu____8482 =
                                                       FStar_Tactics_Types.is_irrelevant
                                                         g in
                                                     Prims.op_Negation
                                                       uu____8482) in
                                                failwhen uu____8480
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____8490 ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____8502 ->
                                                          let uu____8503 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty in
                                                          match uu____8503
                                                          with
                                                          | (t_ps1, t_ty1) ->
                                                              let uu____8518
                                                                =
                                                                FStar_Tactics_Monad.mapM
                                                                  (fun c_lid
                                                                    ->
                                                                    let uu____8546
                                                                    =
                                                                    let uu____8549
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____8549
                                                                    c_lid in
                                                                    match uu____8546
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
                                                                    uu____8622
                                                                    ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty in
                                                                    let uu____8627
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1) in
                                                                    match uu____8627
                                                                    with
                                                                    | 
                                                                    (c_us1,
                                                                    c_ty2) ->
                                                                    let uu____8650
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2 in
                                                                    (match uu____8650
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    comp) ->
                                                                    let uu____8669
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname in
                                                                    let ppname1
                                                                    =
                                                                    let uu____8692
                                                                    =
                                                                    let uu____8697
                                                                    =
                                                                    let uu____8698
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    ppname in
                                                                    Prims.op_Hat
                                                                    "a"
                                                                    uu____8698 in
                                                                    let uu____8699
                                                                    =
                                                                    FStar_Ident.range_of_id
                                                                    ppname in
                                                                    (uu____8697,
                                                                    uu____8699) in
                                                                    FStar_Ident.mk_ident
                                                                    uu____8692 in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    (let uu___1317_8702
                                                                    = bv in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1317_8702.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (uu___1317_8702.FStar_Syntax_Syntax.sort)
                                                                    }) in
                                                                    let bs' =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____8728
                                                                    ->
                                                                    match uu____8728
                                                                    with
                                                                    | 
                                                                    (bv, aq)
                                                                    ->
                                                                    let uu____8747
                                                                    =
                                                                    rename_bv
                                                                    bv in
                                                                    (uu____8747,
                                                                    aq)) bs in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun
                                                                    uu____8772
                                                                    ->
                                                                    fun
                                                                    uu____8773
                                                                    ->
                                                                    match 
                                                                    (uu____8772,
                                                                    uu____8773)
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____8799),
                                                                    (bv',
                                                                    uu____8801))
                                                                    ->
                                                                    let uu____8822
                                                                    =
                                                                    let uu____8829
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv' in
                                                                    (bv,
                                                                    uu____8829) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____8822)
                                                                    bs bs' in
                                                                    let uu____8834
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs' in
                                                                    let uu____8843
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst
                                                                    comp in
                                                                    (uu____8834,
                                                                    uu____8843) in
                                                                    (match uu____8669
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    comp1) ->
                                                                    let uu____8890
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    bs1 in
                                                                    (match uu____8890
                                                                    with
                                                                    | 
                                                                    (d_ps,
                                                                    bs2) ->
                                                                    let uu____8963
                                                                    =
                                                                    let uu____8964
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1 in
                                                                    Prims.op_Negation
                                                                    uu____8964 in
                                                                    failwhen
                                                                    uu____8963
                                                                    "not total?"
                                                                    (fun
                                                                    uu____8981
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
                                                                    uu___6_8997
                                                                    =
                                                                    match uu___6_8997
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____9000)
                                                                    -> true
                                                                    | 
                                                                    uu____9001
                                                                    -> false in
                                                                    let uu____9004
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args in
                                                                    match uu____9004
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
                                                                    uu____9139
                                                                    ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9201
                                                                    ->
                                                                    match uu____9201
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9221),
                                                                    (t,
                                                                    uu____9223))
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
                                                                    uu____9291
                                                                    ->
                                                                    match uu____9291
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9317),
                                                                    (t,
                                                                    uu____9319))
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
                                                                    uu____9374
                                                                    ->
                                                                    match uu____9374
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
                                                                    let uu____9424
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1376_9447
                                                                    = env1 in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.erasable_types_tab);
                                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___1376_9447.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                    }) s_ty1
                                                                    pat in
                                                                    match uu____9424
                                                                    with
                                                                    | 
                                                                    (uu____9460,
                                                                    uu____9461,
                                                                    uu____9462,
                                                                    uu____9463,
                                                                    pat_t,
                                                                    uu____9465,
                                                                    _guard_pat,
                                                                    _erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____9477
                                                                    =
                                                                    let uu____9478
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____9478 in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____9477 in
                                                                    let cod1
                                                                    =
                                                                    let uu____9482
                                                                    =
                                                                    let uu____9491
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b in
                                                                    [uu____9491] in
                                                                    let uu____9510
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____9482
                                                                    uu____9510 in
                                                                    let nty =
                                                                    let uu____9516
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu____9516 in
                                                                    let uu____9519
                                                                    =
                                                                    FStar_Tactics_Monad.new_uvar
                                                                    "destruct branch"
                                                                    env1 nty in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____9519
                                                                    (fun
                                                                    uu____9548
                                                                    ->
                                                                    match uu____9548
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
                                                                    let uu____9574
                                                                    =
                                                                    let uu____9585
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit in
                                                                    [uu____9585] in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____9574 in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1) in
                                                                    let uu____9621
                                                                    =
                                                                    let uu____9632
                                                                    =
                                                                    let uu____9637
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs3) in
                                                                    (fv1,
                                                                    uu____9637) in
                                                                    (g', br,
                                                                    uu____9632) in
                                                                    FStar_Tactics_Monad.ret
                                                                    uu____9621)))))))
                                                                    | 
                                                                    uu____9658
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids in
                                                              FStar_Tactics_Monad.bind
                                                                uu____8518
                                                                (fun goal_brs
                                                                   ->
                                                                   let uu____9707
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs in
                                                                   match uu____9707
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
                                                                    let uu____9780
                                                                    =
                                                                    solve' g
                                                                    w in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____9780
                                                                    (fun
                                                                    uu____9791
                                                                    ->
                                                                    let uu____9792
                                                                    =
                                                                    FStar_Tactics_Monad.add_goals
                                                                    goals in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____9792
                                                                    (fun
                                                                    uu____9802
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    infos)))))
                                            | uu____9809 ->
                                                FStar_Tactics_Monad.fail
                                                  "not an inductive type")))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "destruct") uu____8240
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9854::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9882 = init xs in x :: uu____9882
let rec (inspect :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Tactics_Monad.tac)
  =
  fun t ->
    let uu____9894 =
      let uu____9897 = top_env () in
      FStar_Tactics_Monad.bind uu____9897
        (fun e ->
           let t1 = FStar_Syntax_Util.unascribe t in
           let t2 = FStar_Syntax_Util.un_uinst t1 in
           let t3 = FStar_Syntax_Util.unlazy_emb t2 in
           match t3.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_meta (t4, uu____9913) -> inspect t4
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
               let uu____9978 = last args in
               (match uu____9978 with
                | (a, q) ->
                    let q' = FStar_Reflection_Basic.inspect_aqual q in
                    let uu____10008 =
                      let uu____10009 =
                        let uu____10014 =
                          let uu____10015 = init args in
                          FStar_Syntax_Syntax.mk_Tm_app hd uu____10015
                            t3.FStar_Syntax_Syntax.pos in
                        (uu____10014, (a, q')) in
                      FStar_Reflection_Data.Tv_App uu____10009 in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10008)
           | FStar_Syntax_Syntax.Tm_abs ([], uu____10026, uu____10027) ->
               failwith "empty arguments on Tm_abs"
           | FStar_Syntax_Syntax.Tm_abs (bs, t4, k) ->
               let uu____10079 = FStar_Syntax_Subst.open_term bs t4 in
               (match uu____10079 with
                | (bs1, t5) ->
                    (match bs1 with
                     | [] -> failwith "impossible"
                     | b::bs2 ->
                         let uu____10120 =
                           let uu____10121 =
                             let uu____10126 = FStar_Syntax_Util.abs bs2 t5 k in
                             (b, uu____10126) in
                           FStar_Reflection_Data.Tv_Abs uu____10121 in
                         FStar_All.pipe_left FStar_Tactics_Monad.ret
                           uu____10120))
           | FStar_Syntax_Syntax.Tm_type uu____10129 ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Type ())
           | FStar_Syntax_Syntax.Tm_arrow ([], k) ->
               failwith "empty binders on arrow"
           | FStar_Syntax_Syntax.Tm_arrow uu____10153 ->
               let uu____10168 = FStar_Syntax_Util.arrow_one t3 in
               (match uu____10168 with
                | FStar_Pervasives_Native.Some (b, c) ->
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Arrow (b, c))
                | FStar_Pervasives_Native.None -> failwith "impossible")
           | FStar_Syntax_Syntax.Tm_refine (bv, t4) ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____10198 = FStar_Syntax_Subst.open_term [b] t4 in
               (match uu____10198 with
                | (b', t5) ->
                    let b1 =
                      match b' with
                      | b'1::[] -> b'1
                      | uu____10251 -> failwith "impossible" in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Refine
                         ((FStar_Pervasives_Native.fst b1), t5)))
           | FStar_Syntax_Syntax.Tm_constant c ->
               let uu____10263 =
                 let uu____10264 = FStar_Reflection_Basic.inspect_const c in
                 FStar_Reflection_Data.Tv_Const uu____10264 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10263
           | FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
               let uu____10285 =
                 let uu____10286 =
                   let uu____10291 =
                     let uu____10292 =
                       FStar_Syntax_Unionfind.uvar_id
                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                     FStar_BigInt.of_int_fs uu____10292 in
                   (uu____10291, (ctx_u, s)) in
                 FStar_Reflection_Data.Tv_Uvar uu____10286 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10285
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____10326 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let b = FStar_Syntax_Syntax.mk_binder bv in
                      let uu____10331 = FStar_Syntax_Subst.open_term [b] t21 in
                      (match uu____10331 with
                       | (bs, t22) ->
                           let b1 =
                             match bs with
                             | b1::[] -> b1
                             | uu____10384 ->
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
                  | FStar_Util.Inr uu____10420 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let uu____10424 =
                        FStar_Syntax_Subst.open_let_rec [lb] t21 in
                      (match uu____10424 with
                       | (lbs, t22) ->
                           (match lbs with
                            | lb1::[] ->
                                (match lb1.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____10444 ->
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
                            | uu____10450 ->
                                failwith
                                  "impossible: open_term returned different amount of binders")))
           | FStar_Syntax_Syntax.Tm_match (t4, brs) ->
               let rec inspect_pat p =
                 match p.FStar_Syntax_Syntax.v with
                 | FStar_Syntax_Syntax.Pat_constant c ->
                     let uu____10504 = FStar_Reflection_Basic.inspect_const c in
                     FStar_Reflection_Data.Pat_Constant uu____10504
                 | FStar_Syntax_Syntax.Pat_cons (fv, ps) ->
                     let uu____10523 =
                       let uu____10534 =
                         FStar_List.map
                           (fun uu____10555 ->
                              match uu____10555 with
                              | (p1, b) ->
                                  let uu____10572 = inspect_pat p1 in
                                  (uu____10572, b)) ps in
                       (fv, uu____10534) in
                     FStar_Reflection_Data.Pat_Cons uu____10523
                 | FStar_Syntax_Syntax.Pat_var bv ->
                     FStar_Reflection_Data.Pat_Var bv
                 | FStar_Syntax_Syntax.Pat_wild bv ->
                     FStar_Reflection_Data.Pat_Wild bv
                 | FStar_Syntax_Syntax.Pat_dot_term (bv, t5) ->
                     FStar_Reflection_Data.Pat_Dot_Term (bv, t5) in
               let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
               let brs2 =
                 FStar_List.map
                   (fun uu___7_10666 ->
                      match uu___7_10666 with
                      | (pat, uu____10688, t5) ->
                          let uu____10706 = inspect_pat pat in
                          (uu____10706, t5)) brs1 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Match (t4, brs2))
           | FStar_Syntax_Syntax.Tm_unknown ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 FStar_Reflection_Data.Tv_Unknown
           | uu____10715 ->
               ((let uu____10717 =
                   let uu____10722 =
                     let uu____10723 = FStar_Syntax_Print.tag_of_term t3 in
                     let uu____10724 = term_to_string e t3 in
                     FStar_Util.format2
                       "inspect: outside of expected syntax (%s, %s)\n"
                       uu____10723 uu____10724 in
                   (FStar_Errors.Warning_CantInspect, uu____10722) in
                 FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos
                   uu____10717);
                FStar_All.pipe_left FStar_Tactics_Monad.ret
                  FStar_Reflection_Data.Tv_Unknown)) in
    FStar_Tactics_Monad.wrap_err "inspect" uu____9894
let (pack :
  FStar_Reflection_Data.term_view ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun tv ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10737 = FStar_Syntax_Syntax.bv_to_name bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10737
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10741 = FStar_Syntax_Syntax.bv_to_tm bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10741
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10745 = FStar_Syntax_Syntax.fv_to_tm fv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10745
    | FStar_Reflection_Data.Tv_App (l, (r, q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q in
        let uu____10752 = FStar_Syntax_Util.mk_app l [(r, q')] in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10752
    | FStar_Reflection_Data.Tv_Abs (b, t) ->
        let uu____10777 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10777
    | FStar_Reflection_Data.Tv_Arrow (b, c) ->
        let uu____10794 = FStar_Syntax_Util.arrow [b] c in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10794
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left FStar_Tactics_Monad.ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv, t) ->
        let uu____10813 = FStar_Syntax_Util.refine bv t in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10813
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10817 =
          let uu____10818 =
            let uu____10819 = FStar_Reflection_Basic.pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____10819 in
          FStar_Syntax_Syntax.mk uu____10818 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10817
    | FStar_Reflection_Data.Tv_Uvar (_u, ctx_u_s) ->
        let uu____10824 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10824
    | FStar_Reflection_Data.Tv_Let (false, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____10836 =
          let uu____10837 =
            let uu____10838 =
              let uu____10851 =
                let uu____10854 =
                  let uu____10855 = FStar_Syntax_Syntax.mk_binder bv in
                  [uu____10855] in
                FStar_Syntax_Subst.close uu____10854 t2 in
              ((false, [lb]), uu____10851) in
            FStar_Syntax_Syntax.Tm_let uu____10838 in
          FStar_Syntax_Syntax.mk uu____10837 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10836
    | FStar_Reflection_Data.Tv_Let (true, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____10895 = FStar_Syntax_Subst.close_let_rec [lb] t2 in
        (match uu____10895 with
         | (lbs, body) ->
             let uu____10910 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Range.dummyRange in
             FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10910)
    | FStar_Reflection_Data.Tv_Match (t, brs) ->
        let wrap v =
          {
            FStar_Syntax_Syntax.v = v;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10944 =
                let uu____10945 = FStar_Reflection_Basic.pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____10945 in
              FStar_All.pipe_left wrap uu____10944
          | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
              let uu____10960 =
                let uu____10961 =
                  let uu____10974 =
                    FStar_List.map
                      (fun uu____10995 ->
                         match uu____10995 with
                         | (p1, b) ->
                             let uu____11006 = pack_pat p1 in
                             (uu____11006, b)) ps in
                  (fv, uu____10974) in
                FStar_Syntax_Syntax.Pat_cons uu____10961 in
              FStar_All.pipe_left wrap uu____10960
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv, t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1)) in
        let brs1 =
          FStar_List.map
            (fun uu___8_11052 ->
               match uu___8_11052 with
               | (pat, t1) ->
                   let uu____11069 = pack_pat pat in
                   (uu____11069, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        let uu____11117 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11117
    | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
        let uu____11145 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11145
    | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
        let uu____11191 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11191
    | FStar_Reflection_Data.Tv_Unknown ->
        let uu____11230 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11230
let (lget :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun k ->
      let uu____11247 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps ->
             let uu____11253 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k in
             match uu____11253 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lget") uu____11247
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun _ty ->
    fun k ->
      fun t ->
        let uu____11282 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let ps1 =
                 let uu___1681_11289 = ps in
                 let uu____11290 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___1681_11289.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___1681_11289.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___1681_11289.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___1681_11289.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___1681_11289.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___1681_11289.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___1681_11289.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___1681_11289.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___1681_11289.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___1681_11289.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___1681_11289.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____11290
                 } in
               FStar_Tactics_Monad.set ps1) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lset") uu____11282
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env1 ->
    let uu____11302 = FStar_TypeChecker_Env.clear_expected_typ env1 in
    match uu____11302 with
    | (env2, uu____11310) ->
        let env3 =
          let uu___1688_11316 = env2 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1688_11316.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1688_11316.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1688_11316.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1688_11316.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1688_11316.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1688_11316.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1688_11316.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1688_11316.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1688_11316.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1688_11316.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___1688_11316.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1688_11316.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1688_11316.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1688_11316.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1688_11316.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1688_11316.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1688_11316.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1688_11316.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1688_11316.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1688_11316.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1688_11316.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1688_11316.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1688_11316.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1688_11316.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1688_11316.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1688_11316.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1688_11316.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1688_11316.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1688_11316.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1688_11316.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1688_11316.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1688_11316.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1688_11316.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1688_11316.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1688_11316.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1688_11316.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1688_11316.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1688_11316.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1688_11316.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1688_11316.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1688_11316.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1688_11316.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1688_11316.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1688_11316.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1688_11316.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1688_11316.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        let env4 =
          let uu___1691_11318 = env3 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1691_11318.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1691_11318.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1691_11318.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1691_11318.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1691_11318.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1691_11318.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1691_11318.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1691_11318.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1691_11318.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1691_11318.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1691_11318.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1691_11318.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1691_11318.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1691_11318.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1691_11318.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1691_11318.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1691_11318.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1691_11318.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1691_11318.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1691_11318.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1691_11318.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1691_11318.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1691_11318.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___1691_11318.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1691_11318.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1691_11318.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1691_11318.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1691_11318.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1691_11318.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1691_11318.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1691_11318.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1691_11318.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1691_11318.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1691_11318.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1691_11318.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1691_11318.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1691_11318.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1691_11318.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1691_11318.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1691_11318.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1691_11318.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1691_11318.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1691_11318.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1691_11318.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1691_11318.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1691_11318.FStar_TypeChecker_Env.enable_defer_to_tac)
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
            let uu____11349 =
              FStar_TypeChecker_Env.debug env2
                (FStar_Options.Other "TacVerbose") in
            let uu____11350 = FStar_Util.psmap_empty () in
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
              FStar_Tactics_Types.tac_verb_dbg = uu____11349;
              FStar_Tactics_Types.local_state = uu____11350
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
        let uu____11373 = FStar_Tactics_Types.goal_of_goal_ty env2 typ in
        match uu____11373 with
        | (g, g_u) ->
            let ps =
              proofstate_of_goals rng env2 [g]
                g_u.FStar_TypeChecker_Common.implicits in
            let uu____11385 = FStar_Tactics_Types.goal_witness g in
            (ps, uu____11385)
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
        let goals =
          FStar_List.map (FStar_Tactics_Types.goal_of_implicit env2) imps in
        let w =
          let uu____11410 = FStar_List.hd goals in
          FStar_Tactics_Types.goal_witness uu____11410 in
        let ps =
          let uu____11412 =
            FStar_TypeChecker_Env.debug env2
              (FStar_Options.Other "TacVerbose") in
          let uu____11413 = FStar_Util.psmap_empty () in
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
            FStar_Tactics_Types.tac_verb_dbg = uu____11412;
            FStar_Tactics_Types.local_state = uu____11413
          } in
        (ps, w)