open Prims
let (compress :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun uu___ ->
    (fun t ->
       let uu___ =
         FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
           (Obj.repr ()) in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            uu___
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___1 = Obj.magic uu___1 in
                  let uu___2 = FStar_Syntax_Subst.compress t in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic uu___2))) uu___1))) uu___
let (core_check :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool ->
          (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,
            FStar_TypeChecker_Core.error) FStar_Pervasives.either)
  =
  fun env ->
    fun sol ->
      fun t ->
        fun must_tot ->
          let uu___ =
            let uu___1 = FStar_Options.compat_pre_core_should_check () in
            Prims.op_Negation uu___1 in
          if uu___
          then FStar_Pervasives.Inl FStar_Pervasives_Native.None
          else
            (let debug f =
               let uu___2 = FStar_Options.debug_any () in
               if uu___2 then f () else () in
             let uu___2 =
               FStar_TypeChecker_Core.check_term env sol t must_tot in
             match uu___2 with
             | FStar_Pervasives.Inl (FStar_Pervasives_Native.None) ->
                 FStar_Pervasives.Inl FStar_Pervasives_Native.None
             | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g) ->
                 let uu___3 = FStar_Options.compat_pre_core_set () in
                 if uu___3
                 then FStar_Pervasives.Inl FStar_Pervasives_Native.None
                 else FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g)
             | FStar_Pervasives.Inr err ->
                 (debug
                    (fun uu___4 ->
                       let uu___5 =
                         let uu___6 = FStar_TypeChecker_Env.get_range env in
                         FStar_Class_Show.show
                           FStar_Compiler_Range_Ops.show_range uu___6 in
                       let uu___6 =
                         FStar_TypeChecker_Core.print_error_short err in
                       let uu___7 =
                         FStar_Class_Show.show
                           FStar_Syntax_Print.showable_term sol in
                       let uu___8 =
                         FStar_Class_Show.show
                           FStar_Syntax_Print.showable_term t in
                       let uu___9 = FStar_TypeChecker_Core.print_error err in
                       FStar_Compiler_Util.print5
                         "(%s) Core checking failed (%s) on term %s and type %s\n%s\n"
                         uu___5 uu___6 uu___7 uu___8 uu___9);
                  FStar_Pervasives.Inr err))
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (rangeof : FStar_Tactics_Types.goal -> FStar_Compiler_Range_Type.range) =
  fun g ->
    (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_range
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s -> fun e -> fun t -> FStar_TypeChecker_Normalize.normalize s e t
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
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g ->
    let uu___ =
      let uu___1 = FStar_Tactics_Types.goal_env g in
      let uu___2 = FStar_Tactics_Types.goal_type g in bnorm uu___1 uu___2 in
    FStar_Tactics_Monad.goal_with_type g uu___
let (tacprint : Prims.string -> unit) =
  fun s -> FStar_Compiler_Util.print1 "TAC>> %s\n" s
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      let uu___ = FStar_Compiler_Util.format1 s x in
      FStar_Compiler_Util.print1 "TAC>> %s\n" uu___
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        let uu___ = FStar_Compiler_Util.format2 s x y in
        FStar_Compiler_Util.print1 "TAC>> %s\n" uu___
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        fun z ->
          let uu___ = FStar_Compiler_Util.format3 s x y z in
          FStar_Compiler_Util.print1 "TAC>> %s\n" uu___
let (print : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    (let uu___1 =
       let uu___2 = FStar_Options.silent () in Prims.op_Negation uu___2 in
     if uu___1 then tacprint msg else ());
    FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac () (Obj.repr ())
let (debugging : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            (Obj.magic FStar_Tactics_Monad.get)
            (fun uu___1 ->
               (fun ps ->
                  let ps = Obj.magic ps in
                  let uu___1 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Tac") in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic uu___1))) uu___1))) uu___
let (do_dump_ps : Prims.string -> FStar_Tactics_Types.proofstate -> unit) =
  fun msg ->
    fun ps ->
      let psc = ps.FStar_Tactics_Types.psc in
      let subst = FStar_TypeChecker_Primops_Base.psc_subst psc in
      FStar_Tactics_Printing.do_dump_proofstate ps msg
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
             FStar_Compiler_List.map
               (fun i ->
                  FStar_Tactics_Types.goal_of_implicit
                    ps.FStar_Tactics_Types.main_context i)
               ps.FStar_Tactics_Types.all_implicits in
           let gs1 =
             if print_resolved
             then gs
             else
               FStar_Compiler_List.filter
                 (fun g ->
                    let uu___1 = FStar_Tactics_Types.check_goal_solved g in
                    Prims.op_Negation uu___1) gs in
           let ps' =
             {
               FStar_Tactics_Types.main_context =
                 (ps.FStar_Tactics_Types.main_context);
               FStar_Tactics_Types.all_implicits =
                 (ps.FStar_Tactics_Types.all_implicits);
               FStar_Tactics_Types.goals = gs1;
               FStar_Tactics_Types.smt_goals = [];
               FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
               FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
               FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
               FStar_Tactics_Types.entry_range =
                 (ps.FStar_Tactics_Types.entry_range);
               FStar_Tactics_Types.guard_policy =
                 (ps.FStar_Tactics_Types.guard_policy);
               FStar_Tactics_Types.freshness =
                 (ps.FStar_Tactics_Types.freshness);
               FStar_Tactics_Types.tac_verb_dbg =
                 (ps.FStar_Tactics_Types.tac_verb_dbg);
               FStar_Tactics_Types.local_state =
                 (ps.FStar_Tactics_Types.local_state);
               FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
             } in
           do_dump_ps msg ps'; FStar_Tactics_Result.Success ((), ps))
let (dump_uvars_of :
  FStar_Tactics_Types.goal -> Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun g ->
    fun msg ->
      FStar_Tactics_Monad.mk_tac
        (fun ps ->
           let uvs =
             let uu___ =
               let uu___1 = FStar_Tactics_Types.goal_type g in
               FStar_Syntax_Free.uvars uu___1 in
             FStar_Compiler_Set.elems FStar_Syntax_Free.ord_ctx_uvar uu___ in
           let gs =
             FStar_Compiler_List.map (FStar_Tactics_Types.goal_of_ctx_uvar g)
               uvs in
           let gs1 =
             FStar_Compiler_List.filter
               (fun g1 ->
                  let uu___ = FStar_Tactics_Types.check_goal_solved g1 in
                  Prims.op_Negation uu___) gs in
           let ps' =
             {
               FStar_Tactics_Types.main_context =
                 (ps.FStar_Tactics_Types.main_context);
               FStar_Tactics_Types.all_implicits =
                 (ps.FStar_Tactics_Types.all_implicits);
               FStar_Tactics_Types.goals = gs1;
               FStar_Tactics_Types.smt_goals = [];
               FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
               FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
               FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
               FStar_Tactics_Types.entry_range =
                 (ps.FStar_Tactics_Types.entry_range);
               FStar_Tactics_Types.guard_policy =
                 (ps.FStar_Tactics_Types.guard_policy);
               FStar_Tactics_Types.freshness =
                 (ps.FStar_Tactics_Types.freshness);
               FStar_Tactics_Types.tac_verb_dbg =
                 (ps.FStar_Tactics_Types.tac_verb_dbg);
               FStar_Tactics_Types.local_state =
                 (ps.FStar_Tactics_Types.local_state);
               FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
             } in
           do_dump_ps msg ps'; FStar_Tactics_Result.Success ((), ps))
let fail1 :
  'uuuuu . Prims.string -> Prims.string -> 'uuuuu FStar_Tactics_Monad.tac =
  fun msg ->
    fun x ->
      let uu___ = FStar_Compiler_Util.format1 msg x in
      FStar_Tactics_Monad.fail uu___
let fail2 :
  'uuuuu .
    Prims.string ->
      Prims.string -> Prims.string -> 'uuuuu FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        let uu___ = FStar_Compiler_Util.format2 msg x y in
        FStar_Tactics_Monad.fail uu___
let fail3 :
  'uuuuu .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> 'uuuuu FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          let uu___ = FStar_Compiler_Util.format3 msg x y z in
          FStar_Tactics_Monad.fail uu___
let fail4 :
  'uuuuu .
    Prims.string ->
      Prims.string ->
        Prims.string ->
          Prims.string -> Prims.string -> 'uuuuu FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          fun w ->
            let uu___ = FStar_Compiler_Util.format4 msg x y z w in
            FStar_Tactics_Monad.fail uu___
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu___ = FStar_Syntax_Formula.destruct_typ_as_formula typ in
    match uu___ with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Formula.BaseConn
        (l,
         uu___1::(e1, FStar_Pervasives_Native.None)::(e2,
                                                      FStar_Pervasives_Native.None)::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu___1 ->
        let uu___2 = FStar_Syntax_Util.unb2t typ in
        (match uu___2 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu___3 = FStar_Syntax_Util.head_and_args t in
             (match uu___3 with
              | (hd, args) ->
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStar_Syntax_Subst.compress hd in
                      uu___6.FStar_Syntax_Syntax.n in
                    (uu___5, args) in
                  (match uu___4 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,
                      (uu___5, FStar_Pervasives_Native.Some
                       { FStar_Syntax_Syntax.aqual_implicit = true;
                         FStar_Syntax_Syntax.aqual_attributes = uu___6;_})::
                      (e1, FStar_Pervasives_Native.None)::(e2,
                                                           FStar_Pervasives_Native.None)::[])
                       when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu___5 -> FStar_Pervasives_Native.None)))
let (destruct_eq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun typ ->
      let typ1 = whnf env1 typ in
      let uu___ = destruct_eq' typ1 in
      match uu___ with
      | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
      | FStar_Pervasives_Native.None ->
          let uu___1 = FStar_Syntax_Util.un_squash typ1 in
          (match uu___1 with
           | FStar_Pervasives_Native.Some typ2 ->
               let typ3 = whnf env1 typ2 in destruct_eq' typ3
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (get_guard_policy :
  unit -> FStar_Tactics_Types.guard_policy FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            (Obj.magic FStar_Tactics_Monad.get)
            (fun uu___1 ->
               (fun ps ->
                  let ps = Obj.magic ps in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic ps.FStar_Tactics_Types.guard_policy)))
                 uu___1))) uu___
let (set_guard_policy :
  FStar_Tactics_Types.guard_policy -> unit FStar_Tactics_Monad.tac) =
  fun pol ->
    FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
      (Obj.magic FStar_Tactics_Monad.get)
      (fun uu___ ->
         (fun ps ->
            let ps = Obj.magic ps in
            Obj.magic
              (FStar_Tactics_Monad.set
                 {
                   FStar_Tactics_Types.main_context =
                     (ps.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (ps.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals = (ps.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (ps.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (ps.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (ps.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy = pol;
                   FStar_Tactics_Types.freshness =
                     (ps.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (ps.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (ps.FStar_Tactics_Types.local_state);
                   FStar_Tactics_Types.urgency =
                     (ps.FStar_Tactics_Types.urgency)
                 })) uu___)
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun uu___1 ->
    fun uu___ ->
      (fun pol ->
         fun t ->
           let uu___ = get_guard_policy () in
           Obj.magic
             (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                () (Obj.magic uu___)
                (fun uu___1 ->
                   (fun old_pol ->
                      let old_pol = Obj.magic old_pol in
                      let uu___1 = set_guard_policy pol in
                      Obj.magic
                        (FStar_Class_Monad.op_let_Bang
                           FStar_Tactics_Monad.monad_tac () () uu___1
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 let uu___2 = Obj.magic uu___2 in
                                 Obj.magic
                                   (FStar_Class_Monad.op_let_Bang
                                      FStar_Tactics_Monad.monad_tac () ()
                                      (Obj.magic t)
                                      (fun uu___3 ->
                                         (fun r ->
                                            let r = Obj.magic r in
                                            let uu___3 =
                                              set_guard_policy old_pol in
                                            Obj.magic
                                              (FStar_Class_Monad.op_let_Bang
                                                 FStar_Tactics_Monad.monad_tac
                                                 () () uu___3
                                                 (fun uu___4 ->
                                                    (fun uu___4 ->
                                                       let uu___4 =
                                                         Obj.magic uu___4 in
                                                       Obj.magic
                                                         (FStar_Class_Monad.return
                                                            FStar_Tactics_Monad.monad_tac
                                                            () (Obj.magic r)))
                                                      uu___4))) uu___3)))
                                uu___2))) uu___1))) uu___1 uu___
let (proc_guard_formula :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          -> FStar_Compiler_Range_Type.range -> unit FStar_Tactics_Monad.tac)
  =
  fun reason ->
    fun e ->
      fun f ->
        fun sc_opt ->
          fun rng ->
            FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
              (Obj.magic FStar_Tactics_Monad.get)
              (fun uu___ ->
                 (fun ps ->
                    let ps = Obj.magic ps in
                    match ps.FStar_Tactics_Types.guard_policy with
                    | FStar_Tactics_Types.Drop ->
                        ((let uu___1 =
                            let uu___2 =
                              let uu___3 =
                                FStar_Class_Show.show
                                  FStar_Syntax_Print.showable_term f in
                              FStar_Compiler_Util.format1
                                "Tactics admitted guard <%s>\n\n" uu___3 in
                            (FStar_Errors_Codes.Warning_TacAdmit, uu___2) in
                          FStar_Errors.log_issue
                            e.FStar_TypeChecker_Env.range uu___1);
                         Obj.magic
                           (FStar_Class_Monad.return
                              FStar_Tactics_Monad.monad_tac () (Obj.repr ())))
                    | FStar_Tactics_Types.Goal ->
                        Obj.magic
                          (FStar_Tactics_Monad.mlog
                             (fun uu___ ->
                                let uu___1 =
                                  FStar_Class_Show.show
                                    FStar_Syntax_Print.showable_term f in
                                FStar_Compiler_Util.print2
                                  "Making guard (%s:%s) into a goal\n" reason
                                  uu___1)
                             (fun uu___ ->
                                let uu___1 =
                                  FStar_Tactics_Monad.goal_of_guard reason e
                                    f sc_opt rng in
                                FStar_Class_Monad.op_let_Bang
                                  FStar_Tactics_Monad.monad_tac () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun g ->
                                        let g = Obj.magic g in
                                        Obj.magic
                                          (FStar_Tactics_Monad.push_goals [g]))
                                       uu___2)))
                    | FStar_Tactics_Types.SMT ->
                        Obj.magic
                          (FStar_Tactics_Monad.mlog
                             (fun uu___ ->
                                let uu___1 =
                                  FStar_Class_Show.show
                                    FStar_Syntax_Print.showable_term f in
                                FStar_Compiler_Util.print2
                                  "Pushing guard (%s:%s) as SMT goal\n"
                                  reason uu___1)
                             (fun uu___ ->
                                let uu___1 =
                                  FStar_Tactics_Monad.goal_of_guard reason e
                                    f sc_opt rng in
                                FStar_Class_Monad.op_let_Bang
                                  FStar_Tactics_Monad.monad_tac () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun g ->
                                        let g = Obj.magic g in
                                        Obj.magic
                                          (FStar_Tactics_Monad.push_smt_goals
                                             [g])) uu___2)))
                    | FStar_Tactics_Types.SMTSync ->
                        Obj.magic
                          (FStar_Tactics_Monad.mlog
                             (fun uu___ ->
                                let uu___1 =
                                  FStar_Class_Show.show
                                    FStar_Syntax_Print.showable_term f in
                                FStar_Compiler_Util.print2
                                  "Sending guard (%s:%s) to SMT Synchronously\n"
                                  reason uu___1)
                             (fun uu___ ->
                                let g =
                                  {
                                    FStar_TypeChecker_Common.guard_f =
                                      (FStar_TypeChecker_Common.NonTrivial f);
                                    FStar_TypeChecker_Common.deferred_to_tac
                                      =
                                      (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred_to_tac);
                                    FStar_TypeChecker_Common.deferred =
                                      (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred);
                                    FStar_TypeChecker_Common.univ_ineqs =
                                      (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.univ_ineqs);
                                    FStar_TypeChecker_Common.implicits =
                                      (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.implicits)
                                  } in
                                FStar_TypeChecker_Rel.force_trivial_guard e g;
                                FStar_Class_Monad.return
                                  FStar_Tactics_Monad.monad_tac ()
                                  (Obj.repr ())))
                    | FStar_Tactics_Types.Force ->
                        Obj.magic
                          (FStar_Tactics_Monad.mlog
                             (fun uu___ ->
                                let uu___1 =
                                  FStar_Class_Show.show
                                    FStar_Syntax_Print.showable_term f in
                                FStar_Compiler_Util.print2
                                  "Forcing guard (%s:%s)\n" reason uu___1)
                             (fun uu___ ->
                                let g =
                                  {
                                    FStar_TypeChecker_Common.guard_f =
                                      (FStar_TypeChecker_Common.NonTrivial f);
                                    FStar_TypeChecker_Common.deferred_to_tac
                                      =
                                      (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred_to_tac);
                                    FStar_TypeChecker_Common.deferred =
                                      (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred);
                                    FStar_TypeChecker_Common.univ_ineqs =
                                      (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.univ_ineqs);
                                    FStar_TypeChecker_Common.implicits =
                                      (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.implicits)
                                  } in
                                try
                                  (fun uu___1 ->
                                     match () with
                                     | () ->
                                         let uu___2 =
                                           let uu___3 =
                                             let uu___4 =
                                               FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                 e g in
                                             FStar_TypeChecker_Env.is_trivial
                                               uu___4 in
                                           Prims.op_Negation uu___3 in
                                         if uu___2
                                         then
                                           fail1
                                             "Forcing the guard failed (%s)"
                                             reason
                                         else
                                           FStar_Class_Monad.return
                                             FStar_Tactics_Monad.monad_tac ()
                                             (Obj.repr ())) ()
                                with
                                | uu___1 ->
                                    FStar_Tactics_Monad.mlog
                                      (fun uu___2 ->
                                         let uu___3 =
                                           FStar_Class_Show.show
                                             FStar_Syntax_Print.showable_term
                                             f in
                                         FStar_Compiler_Util.print1
                                           "guard = %s\n" uu___3)
                                      (fun uu___2 ->
                                         fail1
                                           "Forcing the guard failed (%s)"
                                           reason)))) uu___)
let (proc_guard' :
  Prims.bool ->
    Prims.string ->
      env ->
        FStar_TypeChecker_Common.guard_t ->
          FStar_Syntax_Syntax.should_check_uvar
            FStar_Pervasives_Native.option ->
            FStar_Compiler_Range_Type.range -> unit FStar_Tactics_Monad.tac)
  =
  fun simplify ->
    fun reason ->
      fun e ->
        fun g ->
          fun sc_opt ->
            fun rng ->
              FStar_Tactics_Monad.mlog
                (fun uu___ ->
                   let uu___1 = FStar_TypeChecker_Rel.guard_to_string e g in
                   FStar_Compiler_Util.print2 "Processing guard (%s:%s)\n"
                     reason uu___1)
                (fun uu___ ->
                   (match sc_opt with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Allow_untyped r) ->
                        FStar_Compiler_List.iter
                          (fun imp ->
                             FStar_Tactics_Monad.mark_uvar_with_should_check_tag
                               imp.FStar_TypeChecker_Common.imp_uvar
                               (FStar_Syntax_Syntax.Allow_untyped r))
                          g.FStar_TypeChecker_Common.implicits
                    | uu___2 -> ());
                   (let uu___2 =
                      FStar_Tactics_Monad.add_implicits
                        g.FStar_TypeChecker_Common.implicits in
                    FStar_Class_Monad.op_let_Bang
                      FStar_Tactics_Monad.monad_tac () () uu___2
                      (fun uu___3 ->
                         (fun uu___3 ->
                            let uu___3 = Obj.magic uu___3 in
                            let guard_f =
                              if simplify
                              then
                                let uu___4 =
                                  FStar_TypeChecker_Rel.simplify_guard e g in
                                uu___4.FStar_TypeChecker_Common.guard_f
                              else g.FStar_TypeChecker_Common.guard_f in
                            match guard_f with
                            | FStar_TypeChecker_Common.Trivial ->
                                Obj.magic
                                  (FStar_Class_Monad.return
                                     FStar_Tactics_Monad.monad_tac ()
                                     (Obj.repr ()))
                            | FStar_TypeChecker_Common.NonTrivial f ->
                                Obj.magic
                                  (proc_guard_formula reason e f sc_opt rng))
                           uu___3)))
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Common.guard_t ->
        FStar_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          -> FStar_Compiler_Range_Type.range -> unit FStar_Tactics_Monad.tac)
  = proc_guard' true
let (tc_unifier_solved_implicits :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_Syntax_Syntax.ctx_uvar Prims.list ->
          unit FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun must_tot ->
      fun allow_guards ->
        fun uvs ->
          let aux u =
            let dec =
              FStar_Syntax_Unionfind.find_decoration
                u.FStar_Syntax_Syntax.ctx_uvar_head in
            let sc = dec.FStar_Syntax_Syntax.uvar_decoration_should_check in
            match sc with
            | FStar_Syntax_Syntax.Allow_untyped uu___ ->
                FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                  (Obj.repr ())
            | FStar_Syntax_Syntax.Already_checked ->
                FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                  (Obj.repr ())
            | uu___ ->
                let uu___1 =
                  FStar_Syntax_Unionfind.find
                    u.FStar_Syntax_Syntax.ctx_uvar_head in
                (match uu___1 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.repr ())
                 | FStar_Pervasives_Native.Some sol ->
                     let env2 =
                       {
                         FStar_TypeChecker_Env.solver =
                           (env1.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (env1.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (env1.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (env1.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (env1.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (env1.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (env1.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (env1.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (env1.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (env1.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (env1.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (env1.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (env1.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (env1.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (env1.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (env1.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (env1.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (env1.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (env1.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (env1.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (env1.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (env1.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (env1.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (env1.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.intactics =
                           (env1.FStar_TypeChecker_Env.intactics);
                         FStar_TypeChecker_Env.nocoerce =
                           (env1.FStar_TypeChecker_Env.nocoerce);
                         FStar_TypeChecker_Env.tc_term =
                           (env1.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                           (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                         FStar_TypeChecker_Env.universe_of =
                           (env1.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                           =
                           (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                         FStar_TypeChecker_Env.teq_nosmt_force =
                           (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                         FStar_TypeChecker_Env.subtype_nosmt_force =
                           (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (env1.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (env1.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (env1.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (env1.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (env1.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (env1.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (env1.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (env1.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (env1.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (env1.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (env1.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (env1.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (env1.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                         FStar_TypeChecker_Env.unif_allow_ref_guards =
                           (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                         FStar_TypeChecker_Env.erase_erasable_args =
                           (env1.FStar_TypeChecker_Env.erase_erasable_args);
                         FStar_TypeChecker_Env.core_check =
                           (env1.FStar_TypeChecker_Env.core_check)
                       } in
                     let must_tot1 =
                       must_tot &&
                         (Prims.op_Negation
                            (FStar_Syntax_Syntax.uu___is_Allow_ghost
                               dec.FStar_Syntax_Syntax.uvar_decoration_should_check)) in
                     let uu___2 =
                       let uu___3 = FStar_Syntax_Util.ctx_uvar_typ u in
                       core_check env2 sol uu___3 must_tot1 in
                     (match uu___2 with
                      | FStar_Pervasives.Inl (FStar_Pervasives_Native.None)
                          ->
                          (FStar_Tactics_Monad.mark_uvar_as_already_checked u;
                           FStar_Class_Monad.return
                             FStar_Tactics_Monad.monad_tac () (Obj.repr ()))
                      | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g)
                          ->
                          let guard =
                            {
                              FStar_TypeChecker_Common.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial g);
                              FStar_TypeChecker_Common.deferred_to_tac =
                                (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred_to_tac);
                              FStar_TypeChecker_Common.deferred =
                                (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred);
                              FStar_TypeChecker_Common.univ_ineqs =
                                (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.univ_ineqs);
                              FStar_TypeChecker_Common.implicits =
                                (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.implicits)
                            } in
                          let guard1 =
                            FStar_TypeChecker_Rel.simplify_guard env2 guard in
                          let uu___3 =
                            ((FStar_Options.disallow_unification_guards ())
                               && (Prims.op_Negation allow_guards))
                              &&
                              (FStar_TypeChecker_Common.uu___is_NonTrivial
                                 guard1.FStar_TypeChecker_Common.guard_f) in
                          if uu___3
                          then
                            let uu___4 =
                              FStar_Class_Show.show
                                FStar_Syntax_Print.showable_uvar
                                u.FStar_Syntax_Syntax.ctx_uvar_head in
                            let uu___5 =
                              FStar_Class_Show.show
                                FStar_Syntax_Print.showable_term sol in
                            let uu___6 =
                              FStar_Class_Show.show
                                FStar_Syntax_Print.showable_term g in
                            fail3
                              "Could not typecheck unifier solved implicit %s to %s since it produced a guard and guards were not allowed;guard is\n%s"
                              uu___4 uu___5 uu___6
                          else
                            (let uu___5 =
                               proc_guard' false "guard for implicit" env2
                                 guard1 (FStar_Pervasives_Native.Some sc)
                                 u.FStar_Syntax_Syntax.ctx_uvar_range in
                             FStar_Class_Monad.op_let_Bang
                               FStar_Tactics_Monad.monad_tac () () uu___5
                               (fun uu___6 ->
                                  (fun uu___6 ->
                                     let uu___6 = Obj.magic uu___6 in
                                     FStar_Tactics_Monad.mark_uvar_as_already_checked
                                       u;
                                     Obj.magic
                                       (FStar_Class_Monad.return
                                          FStar_Tactics_Monad.monad_tac ()
                                          (Obj.repr ()))) uu___6))
                      | FStar_Pervasives.Inr failed ->
                          let uu___3 =
                            FStar_Class_Show.show
                              FStar_Syntax_Print.showable_uvar
                              u.FStar_Syntax_Syntax.ctx_uvar_head in
                          let uu___4 =
                            FStar_Class_Show.show
                              FStar_Syntax_Print.showable_term sol in
                          let uu___5 =
                            FStar_TypeChecker_Core.print_error failed in
                          fail3
                            "Could not typecheck unifier solved implicit %s to %s because %s"
                            uu___3 uu___4 uu___5)) in
          if env1.FStar_TypeChecker_Env.phase1
          then
            FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
              (Obj.repr ())
          else FStar_Tactics_Monad.iter_tac aux uvs
type check_unifier_solved_implicits_side =
  | Check_none 
  | Check_left_only 
  | Check_right_only 
  | Check_both 
let (uu___is_Check_none : check_unifier_solved_implicits_side -> Prims.bool)
  =
  fun projectee -> match projectee with | Check_none -> true | uu___ -> false
let (uu___is_Check_left_only :
  check_unifier_solved_implicits_side -> Prims.bool) =
  fun projectee ->
    match projectee with | Check_left_only -> true | uu___ -> false
let (uu___is_Check_right_only :
  check_unifier_solved_implicits_side -> Prims.bool) =
  fun projectee ->
    match projectee with | Check_right_only -> true | uu___ -> false
let (uu___is_Check_both : check_unifier_solved_implicits_side -> Prims.bool)
  =
  fun projectee -> match projectee with | Check_both -> true | uu___ -> false
let (__do_unify_wflags :
  Prims.bool ->
    Prims.bool ->
      Prims.bool ->
        check_unifier_solved_implicits_side ->
          env ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term ->
                FStar_TypeChecker_Common.guard_t
                  FStar_Pervasives_Native.option FStar_Tactics_Monad.tac)
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun dbg ->
                   fun allow_guards ->
                     fun must_tot ->
                       fun check_side ->
                         fun env1 ->
                           fun t1 ->
                             fun t2 ->
                               if dbg
                               then
                                 (let uu___1 =
                                    FStar_Class_Show.show
                                      FStar_Syntax_Print.showable_term t1 in
                                  let uu___2 =
                                    FStar_Class_Show.show
                                      FStar_Syntax_Print.showable_term t2 in
                                  FStar_Compiler_Util.print2
                                    "%%%%%%%%do_unify %s =? %s\n" uu___1
                                    uu___2)
                               else ();
                               (let all_uvars =
                                  let uu___1 =
                                    match check_side with
                                    | Check_none ->
                                        FStar_Syntax_Free.new_uv_set ()
                                    | Check_left_only ->
                                        FStar_Syntax_Free.uvars t1
                                    | Check_right_only ->
                                        FStar_Syntax_Free.uvars t2
                                    | Check_both ->
                                        let uu___2 =
                                          FStar_Syntax_Free.uvars t1 in
                                        let uu___3 =
                                          FStar_Syntax_Free.uvars t2 in
                                        FStar_Compiler_Set.union
                                          FStar_Syntax_Free.ord_ctx_uvar
                                          uu___2 uu___3 in
                                  FStar_Compiler_Set.elems
                                    FStar_Syntax_Free.ord_ctx_uvar uu___1 in
                                let uu___1 =
                                  let uu___2 =
                                    let uu___3 =
                                      FStar_Tactics_Monad.trytac
                                        FStar_Tactics_Monad.cur_goal in
                                    Obj.magic
                                      (FStar_Class_Monad.op_let_Bang
                                         FStar_Tactics_Monad.monad_tac () ()
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            (fun gopt ->
                                               let gopt = Obj.magic gopt in
                                               Obj.magic
                                                 (try
                                                    (fun uu___4 ->
                                                       (fun uu___4 ->
                                                          match () with
                                                          | () ->
                                                              let res =
                                                                if
                                                                  allow_guards
                                                                then
                                                                  FStar_TypeChecker_Rel.try_teq
                                                                    true env1
                                                                    t1 t2
                                                                else
                                                                  FStar_TypeChecker_Rel.teq_nosmt
                                                                    env1 t1
                                                                    t2 in
                                                              (if dbg
                                                               then
                                                                 (let uu___6
                                                                    =
                                                                    FStar_Common.string_of_option
                                                                    (FStar_TypeChecker_Rel.guard_to_string
                                                                    env1) res in
                                                                  let uu___7
                                                                    =
                                                                    FStar_Class_Show.show
                                                                    FStar_Syntax_Print.showable_term
                                                                    t1 in
                                                                  let uu___8
                                                                    =
                                                                    FStar_Class_Show.show
                                                                    FStar_Syntax_Print.showable_term
                                                                    t2 in
                                                                  FStar_Compiler_Util.print3
                                                                    "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                                                                    uu___6
                                                                    uu___7
                                                                    uu___8)
                                                               else ();
                                                               (match res
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    FStar_Pervasives_Native.None))
                                                                | FStar_Pervasives_Native.Some
                                                                    g ->
                                                                    let uu___6
                                                                    =
                                                                    tc_unifier_solved_implicits
                                                                    env1
                                                                    must_tot
                                                                    allow_guards
                                                                    all_uvars in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___6
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    uu___7 in
                                                                    let uu___8
                                                                    =
                                                                    FStar_Tactics_Monad.add_implicits
                                                                    g.FStar_TypeChecker_Common.implicits in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___8
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    uu___9 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    (FStar_Pervasives_Native.Some
                                                                    g))))
                                                                    uu___9)))
                                                                    uu___7)))))
                                                         uu___4) ()
                                                  with
                                                  | FStar_Errors.Err
                                                      (uu___5, msg, uu___6)
                                                      ->
                                                      FStar_Tactics_Monad.mlog
                                                        (fun uu___7 ->
                                                           let uu___8 =
                                                             FStar_Errors_Msg.rendermsg
                                                               msg in
                                                           FStar_Compiler_Util.print1
                                                             ">> do_unify error, (%s)\n"
                                                             uu___8)
                                                        (fun uu___7 ->
                                                           (fun uu___7 ->
                                                              Obj.magic
                                                                (FStar_Class_Monad.return
                                                                   FStar_Tactics_Monad.monad_tac
                                                                   ()
                                                                   (Obj.magic
                                                                    FStar_Pervasives_Native.None)))
                                                             uu___7)
                                                  | FStar_Errors.Error
                                                      (uu___5, msg, r,
                                                       uu___6)
                                                      ->
                                                      FStar_Tactics_Monad.mlog
                                                        (fun uu___7 ->
                                                           let uu___8 =
                                                             FStar_Errors_Msg.rendermsg
                                                               msg in
                                                           let uu___9 =
                                                             FStar_Class_Show.show
                                                               FStar_Compiler_Range_Ops.show_range
                                                               r in
                                                           FStar_Compiler_Util.print2
                                                             ">> do_unify error, (%s) at (%s)\n"
                                                             uu___8 uu___9)
                                                        (fun uu___7 ->
                                                           (fun uu___7 ->
                                                              Obj.magic
                                                                (FStar_Class_Monad.return
                                                                   FStar_Tactics_Monad.monad_tac
                                                                   ()
                                                                   (Obj.magic
                                                                    FStar_Pervasives_Native.None)))
                                                             uu___7))) uu___4)) in
                                  FStar_Tactics_Monad.catch uu___2 in
                                Obj.magic
                                  (FStar_Class_Monad.op_let_Bang
                                     FStar_Tactics_Monad.monad_tac () ()
                                     (Obj.magic uu___1)
                                     (fun uu___2 ->
                                        (fun uu___2 ->
                                           let uu___2 = Obj.magic uu___2 in
                                           match uu___2 with
                                           | FStar_Pervasives.Inl exn ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Monad.traise
                                                       exn))
                                           | FStar_Pervasives.Inr v ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Class_Monad.return
                                                       FStar_Tactics_Monad.monad_tac
                                                       () (Obj.magic v))))
                                          uu___2)))) uu___6 uu___5 uu___4
                  uu___3 uu___2 uu___1 uu___
let (__do_unify :
  Prims.bool ->
    Prims.bool ->
      check_unifier_solved_implicits_side ->
        env ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term ->
              FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
                FStar_Tactics_Monad.tac)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun allow_guards ->
                 fun must_tot ->
                   fun check_side ->
                     fun env1 ->
                       fun t1 ->
                         fun t2 ->
                           let dbg =
                             FStar_TypeChecker_Env.debug env1
                               (FStar_Options.Other "TacUnify") in
                           let uu___ =
                             FStar_Class_Monad.return
                               FStar_Tactics_Monad.monad_tac () (Obj.repr ()) in
                           Obj.magic
                             (FStar_Class_Monad.op_let_Bang
                                FStar_Tactics_Monad.monad_tac () () uu___
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      let uu___1 = Obj.magic uu___1 in
                                      if dbg
                                      then
                                        (FStar_Options.push ();
                                         (let uu___4 =
                                            FStar_Options.set_options
                                              "--debug_level Rel --debug_level RelCheck" in
                                          ()))
                                      else ();
                                      (let uu___3 =
                                         __do_unify_wflags dbg allow_guards
                                           must_tot check_side env1 t1 t2 in
                                       Obj.magic
                                         (FStar_Class_Monad.op_let_Bang
                                            FStar_Tactics_Monad.monad_tac ()
                                            () (Obj.magic uu___3)
                                            (fun uu___4 ->
                                               (fun r ->
                                                  let r = Obj.magic r in
                                                  if dbg
                                                  then FStar_Options.pop ()
                                                  else ();
                                                  Obj.magic
                                                    (FStar_Class_Monad.return
                                                       FStar_Tactics_Monad.monad_tac
                                                       () (Obj.magic r)))
                                                 uu___4)))) uu___1))) uu___5
                uu___4 uu___3 uu___2 uu___1 uu___
let (do_unify_aux :
  Prims.bool ->
    check_unifier_solved_implicits_side ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun must_tot ->
               fun check_side ->
                 fun env1 ->
                   fun t1 ->
                     fun t2 ->
                       let uu___ =
                         __do_unify false must_tot check_side env1 t1 t2 in
                       Obj.magic
                         (FStar_Class_Monad.op_let_Bang
                            FStar_Tactics_Monad.monad_tac () ()
                            (Obj.magic uu___)
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  let uu___1 = Obj.magic uu___1 in
                                  match uu___1 with
                                  | FStar_Pervasives_Native.None ->
                                      Obj.magic
                                        (FStar_Class_Monad.return
                                           FStar_Tactics_Monad.monad_tac ()
                                           (Obj.magic false))
                                  | FStar_Pervasives_Native.Some g ->
                                      let uu___2 =
                                        let uu___3 =
                                          let uu___4 =
                                            FStar_TypeChecker_Env.is_trivial_guard_formula
                                              g in
                                          Prims.op_Negation uu___4 in
                                        if uu___3
                                        then
                                          FStar_Compiler_Effect.failwith
                                            "internal error: do_unify: guard is not trivial"
                                        else
                                          FStar_Class_Monad.return
                                            FStar_Tactics_Monad.monad_tac ()
                                            (Obj.repr ()) in
                                      Obj.magic
                                        (FStar_Class_Monad.op_let_Bang
                                           FStar_Tactics_Monad.monad_tac ()
                                           () uu___2
                                           (fun uu___3 ->
                                              (fun uu___3 ->
                                                 let uu___3 =
                                                   Obj.magic uu___3 in
                                                 Obj.magic
                                                   (FStar_Class_Monad.return
                                                      FStar_Tactics_Monad.monad_tac
                                                      () (Obj.magic true)))
                                                uu___3))) uu___1))) uu___4
              uu___3 uu___2 uu___1 uu___
let (do_unify :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun must_tot ->
    fun env1 ->
      fun t1 -> fun t2 -> do_unify_aux must_tot Check_both env1 t1 t2
let (do_unify_maybe_guards :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
              FStar_Tactics_Monad.tac)
  =
  fun allow_guards ->
    fun must_tot ->
      fun env1 ->
        fun t1 ->
          fun t2 -> __do_unify allow_guards must_tot Check_both env1 t1 t2
let (do_match :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun must_tot ->
             fun env1 ->
               fun t1 ->
                 fun t2 ->
                   let uu___ =
                     FStar_Tactics_Monad.mk_tac
                       (fun ps ->
                          let tx = FStar_Syntax_Unionfind.new_transaction () in
                          FStar_Tactics_Result.Success (tx, ps)) in
                   Obj.magic
                     (FStar_Class_Monad.op_let_Bang
                        FStar_Tactics_Monad.monad_tac () () (Obj.magic uu___)
                        (fun uu___1 ->
                           (fun tx ->
                              let tx = Obj.magic tx in
                              let uvs1 = FStar_Syntax_Free.uvars_uncached t1 in
                              let uu___1 =
                                do_unify_aux must_tot Check_right_only env1
                                  t1 t2 in
                              Obj.magic
                                (FStar_Class_Monad.op_let_Bang
                                   FStar_Tactics_Monad.monad_tac () ()
                                   (Obj.magic uu___1)
                                   (fun uu___2 ->
                                      (fun r ->
                                         let r = Obj.magic r in
                                         if r
                                         then
                                           let uvs2 =
                                             FStar_Syntax_Free.uvars_uncached
                                               t1 in
                                           let uu___2 =
                                             let uu___3 =
                                               FStar_Compiler_Set.equal
                                                 FStar_Syntax_Free.ord_ctx_uvar
                                                 uvs1 uvs2 in
                                             Prims.op_Negation uu___3 in
                                           (if uu___2
                                            then
                                              (FStar_Syntax_Unionfind.rollback
                                                 tx;
                                               Obj.magic
                                                 (FStar_Class_Monad.return
                                                    FStar_Tactics_Monad.monad_tac
                                                    () (Obj.magic false)))
                                            else
                                              Obj.magic
                                                (FStar_Class_Monad.return
                                                   FStar_Tactics_Monad.monad_tac
                                                   () (Obj.magic true)))
                                         else
                                           Obj.magic
                                             (FStar_Class_Monad.return
                                                FStar_Tactics_Monad.monad_tac
                                                () (Obj.magic false))) uu___2)))
                             uu___1))) uu___3 uu___2 uu___1 uu___
let (do_match_on_lhs :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun must_tot ->
             fun env1 ->
               fun t1 ->
                 fun t2 ->
                   let uu___ =
                     FStar_Tactics_Monad.mk_tac
                       (fun ps ->
                          let tx = FStar_Syntax_Unionfind.new_transaction () in
                          FStar_Tactics_Result.Success (tx, ps)) in
                   Obj.magic
                     (FStar_Class_Monad.op_let_Bang
                        FStar_Tactics_Monad.monad_tac () () (Obj.magic uu___)
                        (fun uu___1 ->
                           (fun tx ->
                              let tx = Obj.magic tx in
                              let uu___1 = destruct_eq env1 t1 in
                              match uu___1 with
                              | FStar_Pervasives_Native.None ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Monad.fail
                                          "do_match_on_lhs: not an eq"))
                              | FStar_Pervasives_Native.Some (lhs, uu___2) ->
                                  Obj.magic
                                    (Obj.repr
                                       (let uvs1 =
                                          FStar_Syntax_Free.uvars_uncached
                                            lhs in
                                        let uu___3 =
                                          do_unify_aux must_tot
                                            Check_right_only env1 t1 t2 in
                                        FStar_Class_Monad.op_let_Bang
                                          FStar_Tactics_Monad.monad_tac () ()
                                          (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             (fun r ->
                                                let r = Obj.magic r in
                                                if r
                                                then
                                                  let uvs2 =
                                                    FStar_Syntax_Free.uvars_uncached
                                                      lhs in
                                                  let uu___4 =
                                                    let uu___5 =
                                                      FStar_Compiler_Set.equal
                                                        FStar_Syntax_Free.ord_ctx_uvar
                                                        uvs1 uvs2 in
                                                    Prims.op_Negation uu___5 in
                                                  (if uu___4
                                                   then
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      Obj.magic
                                                        (FStar_Class_Monad.return
                                                           FStar_Tactics_Monad.monad_tac
                                                           ()
                                                           (Obj.magic false)))
                                                   else
                                                     Obj.magic
                                                       (FStar_Class_Monad.return
                                                          FStar_Tactics_Monad.monad_tac
                                                          () (Obj.magic true)))
                                                else
                                                  Obj.magic
                                                    (FStar_Class_Monad.return
                                                       FStar_Tactics_Monad.monad_tac
                                                       () (Obj.magic false)))
                                               uu___4)))) uu___1))) uu___3
            uu___2 uu___1 uu___
let (set_solution :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu___ =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
      match uu___ with
      | FStar_Pervasives_Native.Some uu___1 ->
          let uu___2 =
            let uu___3 = FStar_Tactics_Printing.goal_to_string_verbose goal in
            FStar_Compiler_Util.format1 "Goal %s is already solved" uu___3 in
          FStar_Tactics_Monad.fail uu___2
      | FStar_Pervasives_Native.None ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           FStar_Tactics_Monad.mark_goal_implicit_already_checked goal;
           FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
             (Obj.repr ()))
let (trysolve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let must_tot = true in
      let uu___ = FStar_Tactics_Types.goal_env goal in
      let uu___1 = FStar_Tactics_Types.goal_witness goal in
      do_unify must_tot uu___ solution uu___1
let (solve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let e = FStar_Tactics_Types.goal_env goal in
      FStar_Tactics_Monad.mlog
        (fun uu___ ->
           let uu___1 =
             let uu___2 = FStar_Tactics_Types.goal_witness goal in
             FStar_Class_Show.show FStar_Syntax_Print.showable_term uu___2 in
           let uu___2 =
             FStar_Class_Show.show FStar_Syntax_Print.showable_term solution in
           FStar_Compiler_Util.print2 "solve %s := %s\n" uu___1 uu___2)
        (fun uu___ ->
           let uu___1 = trysolve goal solution in
           FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
             (Obj.magic uu___1)
             (fun uu___2 ->
                (fun b ->
                   let b = Obj.magic b in
                   if b
                   then
                     Obj.magic
                       (FStar_Class_Monad.op_let_Bang
                          FStar_Tactics_Monad.monad_tac () ()
                          FStar_Tactics_Monad.dismiss
                          (fun uu___2 ->
                             (fun uu___2 ->
                                let uu___2 = Obj.magic uu___2 in
                                Obj.magic
                                  FStar_Tactics_Monad.remove_solved_goals)
                               uu___2))
                   else
                     (let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Tactics_Types.goal_env goal in
                          tts uu___5 solution in
                        let uu___5 =
                          let uu___6 = FStar_Tactics_Types.goal_env goal in
                          let uu___7 = FStar_Tactics_Types.goal_witness goal in
                          tts uu___6 uu___7 in
                        let uu___6 =
                          let uu___7 = FStar_Tactics_Types.goal_env goal in
                          let uu___8 = FStar_Tactics_Types.goal_type goal in
                          tts uu___7 uu___8 in
                        FStar_Compiler_Util.format3
                          "%s does not solve %s : %s" uu___4 uu___5 uu___6 in
                      Obj.magic (FStar_Tactics_Monad.fail uu___3))) uu___2))
let (solve' :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu___ = set_solution goal solution in
      FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () () uu___
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___1 = Obj.magic uu___1 in
              Obj.magic
                (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac
                   () () FStar_Tactics_Monad.dismiss
                   (fun uu___2 ->
                      (fun uu___2 ->
                         let uu___2 = Obj.magic uu___2 in
                         Obj.magic FStar_Tactics_Monad.remove_solved_goals)
                        uu___2))) uu___1)
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.un_squash t1 in
    match uu___ with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t' in
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress t'1 in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu___2 -> false)
    | uu___1 -> false
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = FStar_Syntax_Util.un_squash t in
    match uu___ with
    | FStar_Pervasives_Native.Some t' ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress t' in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu___2 -> false)
    | uu___1 -> false
let meas :
  'a .
    Prims.string -> 'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun s ->
    fun f ->
      FStar_Tactics_Monad.mk_tac
        (fun ps ->
           let uu___ =
             FStar_Compiler_Util.record_time
               (fun uu___1 -> FStar_Tactics_Monad.run f ps) in
           match uu___ with
           | (r, ms) ->
               ((let uu___2 =
                   FStar_Class_Show.show
                     (FStar_Class_Show.printableshow
                        FStar_Class_Printable.printable_int) ms in
                 FStar_Compiler_Util.print2 "++ Tactic %s ran in \t\t%sms\n"
                   s uu___2);
                r))
let (tadmit_t : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu___ =
      FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
        (Obj.magic FStar_Tactics_Monad.get)
        (fun uu___1 ->
           (fun ps ->
              let ps = Obj.magic ps in
              Obj.magic
                (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac
                   () () (Obj.magic FStar_Tactics_Monad.cur_goal)
                   (fun uu___1 ->
                      (fun g ->
                         let g = Obj.magic g in
                         (let uu___2 =
                            let uu___3 = FStar_Tactics_Types.goal_type g in
                            FStar_Class_HasRange.pos
                              (FStar_Syntax_Syntax.has_range_syntax ())
                              uu___3 in
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                FStar_Tactics_Printing.goal_to_string ""
                                  FStar_Pervasives_Native.None ps g in
                              FStar_Compiler_Util.format1
                                "Tactics admitted goal <%s>\n\n" uu___5 in
                            (FStar_Errors_Codes.Warning_TacAdmit, uu___4) in
                          FStar_Errors.log_issue uu___2 uu___3);
                         Obj.magic (solve' g t)) uu___1))) uu___1) in
    FStar_Tactics_Monad.wrap_err "tadmit_t" uu___
let (fresh : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            (Obj.magic FStar_Tactics_Monad.get)
            (fun uu___1 ->
               (fun ps ->
                  let ps = Obj.magic ps in
                  let n = ps.FStar_Tactics_Types.freshness in
                  let ps1 =
                    {
                      FStar_Tactics_Types.main_context =
                        (ps.FStar_Tactics_Types.main_context);
                      FStar_Tactics_Types.all_implicits =
                        (ps.FStar_Tactics_Types.all_implicits);
                      FStar_Tactics_Types.goals =
                        (ps.FStar_Tactics_Types.goals);
                      FStar_Tactics_Types.smt_goals =
                        (ps.FStar_Tactics_Types.smt_goals);
                      FStar_Tactics_Types.depth =
                        (ps.FStar_Tactics_Types.depth);
                      FStar_Tactics_Types.__dump =
                        (ps.FStar_Tactics_Types.__dump);
                      FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
                      FStar_Tactics_Types.entry_range =
                        (ps.FStar_Tactics_Types.entry_range);
                      FStar_Tactics_Types.guard_policy =
                        (ps.FStar_Tactics_Types.guard_policy);
                      FStar_Tactics_Types.freshness = (n + Prims.int_one);
                      FStar_Tactics_Types.tac_verb_dbg =
                        (ps.FStar_Tactics_Types.tac_verb_dbg);
                      FStar_Tactics_Types.local_state =
                        (ps.FStar_Tactics_Types.local_state);
                      FStar_Tactics_Types.urgency =
                        (ps.FStar_Tactics_Types.urgency)
                    } in
                  let uu___1 = FStar_Tactics_Monad.set ps1 in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang
                       FStar_Tactics_Monad.monad_tac () () uu___1
                       (fun uu___2 ->
                          (fun uu___2 ->
                             let uu___2 = Obj.magic uu___2 in
                             let uu___3 = FStar_BigInt.of_int_fs n in
                             Obj.magic
                               (FStar_Class_Monad.return
                                  FStar_Tactics_Monad.monad_tac ()
                                  (Obj.magic uu___3))) uu___2))) uu___1)))
      uu___
let (curms : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun uu___ ->
       let uu___1 =
         let uu___2 = FStar_Compiler_Util.now_ms () in
         FStar_BigInt.of_int_fs uu___2 in
       Obj.magic
         (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
            (Obj.magic uu___1))) uu___
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun e ->
         fun t ->
           Obj.magic
             (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                () (Obj.magic FStar_Tactics_Monad.get)
                (fun uu___ ->
                   (fun ps ->
                      let ps = Obj.magic ps in
                      Obj.magic
                        (FStar_Tactics_Monad.mlog
                           (fun uu___ ->
                              let uu___1 =
                                FStar_Class_Show.show
                                  FStar_Syntax_Print.showable_term t in
                              FStar_Compiler_Util.print1 "Tac> __tc(%s)\n"
                                uu___1)
                           (fun uu___ ->
                              let e1 =
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (e.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (e.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (e.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (e.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (e.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (e.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (e.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (e.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (e.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (e.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (e.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (e.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (e.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (e.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (e.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (e.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (e.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (e.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (e.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (e.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (e.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (e.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (e.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (e.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    false;
                                  FStar_TypeChecker_Env.intactics =
                                    (e.FStar_TypeChecker_Env.intactics);
                                  FStar_TypeChecker_Env.nocoerce =
                                    (e.FStar_TypeChecker_Env.nocoerce);
                                  FStar_TypeChecker_Env.tc_term =
                                    (e.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                    =
                                    (e.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.universe_of =
                                    (e.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                    =
                                    (e.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.teq_nosmt_force =
                                    (e.FStar_TypeChecker_Env.teq_nosmt_force);
                                  FStar_TypeChecker_Env.subtype_nosmt_force =
                                    (e.FStar_TypeChecker_Env.subtype_nosmt_force);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (e.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (e.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (e.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (e.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (e.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (e.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (e.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (e.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (e.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (e.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (e.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (e.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (e.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (e.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (e.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (e.FStar_TypeChecker_Env.enable_defer_to_tac);
                                  FStar_TypeChecker_Env.unif_allow_ref_guards
                                    =
                                    (e.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                  FStar_TypeChecker_Env.erase_erasable_args =
                                    (e.FStar_TypeChecker_Env.erase_erasable_args);
                                  FStar_TypeChecker_Env.core_check =
                                    (e.FStar_TypeChecker_Env.core_check)
                                } in
                              try
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      match () with
                                      | () ->
                                          let uu___2 =
                                            FStar_TypeChecker_TcTerm.typeof_tot_or_gtot_term
                                              e1 t true in
                                          Obj.magic
                                            (FStar_Class_Monad.return
                                               FStar_Tactics_Monad.monad_tac
                                               () (Obj.magic uu___2))) uu___1)
                                  ()
                              with
                              | FStar_Errors.Err (uu___2, msg, uu___3) ->
                                  let uu___4 = tts e1 t in
                                  let uu___5 =
                                    let uu___6 =
                                      FStar_TypeChecker_Env.all_binders e1 in
                                    FStar_Syntax_Print.binders_to_string ", "
                                      uu___6 in
                                  let uu___6 = FStar_Errors_Msg.rendermsg msg in
                                  fail3
                                    "Cannot type (1) %s in context (%s). Error = (%s)"
                                    uu___4 uu___5 uu___6
                              | FStar_Errors.Error
                                  (uu___2, msg, uu___3, uu___4) ->
                                  let uu___5 = tts e1 t in
                                  let uu___6 =
                                    let uu___7 =
                                      FStar_TypeChecker_Env.all_binders e1 in
                                    FStar_Syntax_Print.binders_to_string ", "
                                      uu___7 in
                                  let uu___7 = FStar_Errors_Msg.rendermsg msg in
                                  fail3
                                    "Cannot type (1) %s in context (%s). Error = (%s)"
                                    uu___5 uu___6 uu___7))) uu___))) uu___1
        uu___
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun e ->
         fun t ->
           Obj.magic
             (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                () (Obj.magic FStar_Tactics_Monad.get)
                (fun uu___ ->
                   (fun ps ->
                      let ps = Obj.magic ps in
                      Obj.magic
                        (FStar_Tactics_Monad.mlog
                           (fun uu___ ->
                              let uu___1 =
                                FStar_Class_Show.show
                                  FStar_Syntax_Print.showable_term t in
                              FStar_Compiler_Util.print1
                                "Tac> __tc_ghost(%s)\n" uu___1)
                           (fun uu___ ->
                              let e1 =
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (e.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (e.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (e.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (e.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (e.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (e.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (e.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (e.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (e.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (e.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (e.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (e.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (e.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (e.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (e.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (e.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (e.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (e.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (e.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (e.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (e.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (e.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (e.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (e.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    false;
                                  FStar_TypeChecker_Env.intactics =
                                    (e.FStar_TypeChecker_Env.intactics);
                                  FStar_TypeChecker_Env.nocoerce =
                                    (e.FStar_TypeChecker_Env.nocoerce);
                                  FStar_TypeChecker_Env.tc_term =
                                    (e.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                    =
                                    (e.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.universe_of =
                                    (e.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                    =
                                    (e.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.teq_nosmt_force =
                                    (e.FStar_TypeChecker_Env.teq_nosmt_force);
                                  FStar_TypeChecker_Env.subtype_nosmt_force =
                                    (e.FStar_TypeChecker_Env.subtype_nosmt_force);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (e.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (e.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (e.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (e.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (e.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (e.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (e.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (e.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (e.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (e.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (e.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (e.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (e.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (e.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (e.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (e.FStar_TypeChecker_Env.enable_defer_to_tac);
                                  FStar_TypeChecker_Env.unif_allow_ref_guards
                                    =
                                    (e.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                  FStar_TypeChecker_Env.erase_erasable_args =
                                    (e.FStar_TypeChecker_Env.erase_erasable_args);
                                  FStar_TypeChecker_Env.core_check =
                                    (e.FStar_TypeChecker_Env.core_check)
                                } in
                              let e2 =
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (e1.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (e1.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (e1.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (e1.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (e1.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (e1.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (e1.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (e1.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (e1.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (e1.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (e1.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (e1.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (e1.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs = [];
                                  FStar_TypeChecker_Env.top_level =
                                    (e1.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (e1.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (e1.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (e1.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (e1.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (e1.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (e1.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (e1.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (e1.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (e1.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (e1.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.intactics =
                                    (e1.FStar_TypeChecker_Env.intactics);
                                  FStar_TypeChecker_Env.nocoerce =
                                    (e1.FStar_TypeChecker_Env.nocoerce);
                                  FStar_TypeChecker_Env.tc_term =
                                    (e1.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                    =
                                    (e1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.universe_of =
                                    (e1.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                    =
                                    (e1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.teq_nosmt_force =
                                    (e1.FStar_TypeChecker_Env.teq_nosmt_force);
                                  FStar_TypeChecker_Env.subtype_nosmt_force =
                                    (e1.FStar_TypeChecker_Env.subtype_nosmt_force);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (e1.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (e1.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (e1.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (e1.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (e1.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (e1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (e1.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (e1.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (e1.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (e1.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (e1.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (e1.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (e1.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (e1.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (e1.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (e1.FStar_TypeChecker_Env.enable_defer_to_tac);
                                  FStar_TypeChecker_Env.unif_allow_ref_guards
                                    =
                                    (e1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                  FStar_TypeChecker_Env.erase_erasable_args =
                                    (e1.FStar_TypeChecker_Env.erase_erasable_args);
                                  FStar_TypeChecker_Env.core_check =
                                    (e1.FStar_TypeChecker_Env.core_check)
                                } in
                              try
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      match () with
                                      | () ->
                                          let uu___2 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              e2 t in
                                          (match uu___2 with
                                           | (t1, lc, g) ->
                                               Obj.magic
                                                 (FStar_Class_Monad.return
                                                    FStar_Tactics_Monad.monad_tac
                                                    ()
                                                    (Obj.magic
                                                       (t1,
                                                         (lc.FStar_TypeChecker_Common.res_typ),
                                                         g))))) uu___1) ()
                              with
                              | FStar_Errors.Err (uu___2, msg, uu___3) ->
                                  let uu___4 = tts e2 t in
                                  let uu___5 =
                                    let uu___6 =
                                      FStar_TypeChecker_Env.all_binders e2 in
                                    FStar_Syntax_Print.binders_to_string ", "
                                      uu___6 in
                                  let uu___6 = FStar_Errors_Msg.rendermsg msg in
                                  fail3
                                    "Cannot type (2) %s in context (%s). Error = (%s)"
                                    uu___4 uu___5 uu___6
                              | FStar_Errors.Error
                                  (uu___2, msg, uu___3, uu___4) ->
                                  let uu___5 = tts e2 t in
                                  let uu___6 =
                                    let uu___7 =
                                      FStar_TypeChecker_Env.all_binders e2 in
                                    FStar_Syntax_Print.binders_to_string ", "
                                      uu___7 in
                                  let uu___7 = FStar_Errors_Msg.rendermsg msg in
                                  fail3
                                    "Cannot type (2) %s in context (%s). Error = (%s)"
                                    uu___5 uu___6 uu___7))) uu___))) uu___1
        uu___
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun e ->
         fun t ->
           Obj.magic
             (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                () (Obj.magic FStar_Tactics_Monad.get)
                (fun uu___ ->
                   (fun ps ->
                      let ps = Obj.magic ps in
                      Obj.magic
                        (FStar_Tactics_Monad.mlog
                           (fun uu___ ->
                              let uu___1 =
                                FStar_Class_Show.show
                                  FStar_Syntax_Print.showable_term t in
                              let uu___2 =
                                let uu___3 =
                                  FStar_TypeChecker_Env.all_binders e in
                                FStar_Syntax_Print.binders_to_string ", "
                                  uu___3 in
                              FStar_Compiler_Util.print2
                                "Tac> __tc_lax(%s)(Context:%s)\n" uu___1
                                uu___2)
                           (fun uu___ ->
                              let e1 =
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (e.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (e.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (e.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (e.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (e.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (e.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (e.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (e.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (e.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (e.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (e.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (e.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (e.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (e.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (e.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (e.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (e.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (e.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (e.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (e.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (e.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (e.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (e.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (e.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    false;
                                  FStar_TypeChecker_Env.intactics =
                                    (e.FStar_TypeChecker_Env.intactics);
                                  FStar_TypeChecker_Env.nocoerce =
                                    (e.FStar_TypeChecker_Env.nocoerce);
                                  FStar_TypeChecker_Env.tc_term =
                                    (e.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                    =
                                    (e.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.universe_of =
                                    (e.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                    =
                                    (e.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.teq_nosmt_force =
                                    (e.FStar_TypeChecker_Env.teq_nosmt_force);
                                  FStar_TypeChecker_Env.subtype_nosmt_force =
                                    (e.FStar_TypeChecker_Env.subtype_nosmt_force);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (e.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (e.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (e.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (e.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (e.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (e.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (e.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (e.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (e.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (e.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (e.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (e.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (e.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (e.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (e.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (e.FStar_TypeChecker_Env.enable_defer_to_tac);
                                  FStar_TypeChecker_Env.unif_allow_ref_guards
                                    =
                                    (e.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                  FStar_TypeChecker_Env.erase_erasable_args =
                                    (e.FStar_TypeChecker_Env.erase_erasable_args);
                                  FStar_TypeChecker_Env.core_check =
                                    (e.FStar_TypeChecker_Env.core_check)
                                } in
                              let e2 =
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (e1.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (e1.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (e1.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (e1.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (e1.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (e1.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (e1.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (e1.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (e1.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (e1.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (e1.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (e1.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (e1.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (e1.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (e1.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (e1.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (e1.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (e1.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (e1.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (e1.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (e1.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (e1.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (e1.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (e1.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.intactics =
                                    (e1.FStar_TypeChecker_Env.intactics);
                                  FStar_TypeChecker_Env.nocoerce =
                                    (e1.FStar_TypeChecker_Env.nocoerce);
                                  FStar_TypeChecker_Env.tc_term =
                                    (e1.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                    =
                                    (e1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.universe_of =
                                    (e1.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                    =
                                    (e1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.teq_nosmt_force =
                                    (e1.FStar_TypeChecker_Env.teq_nosmt_force);
                                  FStar_TypeChecker_Env.subtype_nosmt_force =
                                    (e1.FStar_TypeChecker_Env.subtype_nosmt_force);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (e1.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (e1.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (e1.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (e1.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (e1.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (e1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (e1.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (e1.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (e1.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (e1.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (e1.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (e1.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (e1.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (e1.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (e1.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (e1.FStar_TypeChecker_Env.enable_defer_to_tac);
                                  FStar_TypeChecker_Env.unif_allow_ref_guards
                                    =
                                    (e1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                  FStar_TypeChecker_Env.erase_erasable_args =
                                    (e1.FStar_TypeChecker_Env.erase_erasable_args);
                                  FStar_TypeChecker_Env.core_check =
                                    (e1.FStar_TypeChecker_Env.core_check)
                                } in
                              let e3 =
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (e2.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (e2.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (e2.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (e2.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (e2.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (e2.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (e2.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (e2.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (e2.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (e2.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (e2.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (e2.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (e2.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs = [];
                                  FStar_TypeChecker_Env.top_level =
                                    (e2.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (e2.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (e2.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (e2.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (e2.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (e2.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (e2.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (e2.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (e2.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (e2.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (e2.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.intactics =
                                    (e2.FStar_TypeChecker_Env.intactics);
                                  FStar_TypeChecker_Env.nocoerce =
                                    (e2.FStar_TypeChecker_Env.nocoerce);
                                  FStar_TypeChecker_Env.tc_term =
                                    (e2.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                    =
                                    (e2.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.universe_of =
                                    (e2.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                    =
                                    (e2.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.teq_nosmt_force =
                                    (e2.FStar_TypeChecker_Env.teq_nosmt_force);
                                  FStar_TypeChecker_Env.subtype_nosmt_force =
                                    (e2.FStar_TypeChecker_Env.subtype_nosmt_force);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (e2.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (e2.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (e2.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (e2.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (e2.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (e2.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (e2.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (e2.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (e2.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (e2.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (e2.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (e2.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (e2.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (e2.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (e2.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (e2.FStar_TypeChecker_Env.enable_defer_to_tac);
                                  FStar_TypeChecker_Env.unif_allow_ref_guards
                                    =
                                    (e2.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                  FStar_TypeChecker_Env.erase_erasable_args =
                                    (e2.FStar_TypeChecker_Env.erase_erasable_args);
                                  FStar_TypeChecker_Env.core_check =
                                    (e2.FStar_TypeChecker_Env.core_check)
                                } in
                              try
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      match () with
                                      | () ->
                                          let uu___2 =
                                            FStar_TypeChecker_TcTerm.tc_term
                                              e3 t in
                                          Obj.magic
                                            (FStar_Class_Monad.return
                                               FStar_Tactics_Monad.monad_tac
                                               () (Obj.magic uu___2))) uu___1)
                                  ()
                              with
                              | FStar_Errors.Err (uu___2, msg, uu___3) ->
                                  let uu___4 = tts e3 t in
                                  let uu___5 =
                                    let uu___6 =
                                      FStar_TypeChecker_Env.all_binders e3 in
                                    FStar_Syntax_Print.binders_to_string ", "
                                      uu___6 in
                                  let uu___6 = FStar_Errors_Msg.rendermsg msg in
                                  fail3
                                    "Cannot type (3) %s in context (%s). Error = (%s)"
                                    uu___4 uu___5 uu___6
                              | FStar_Errors.Error
                                  (uu___2, msg, uu___3, uu___4) ->
                                  let uu___5 = tts e3 t in
                                  let uu___6 =
                                    let uu___7 =
                                      FStar_TypeChecker_Env.all_binders e3 in
                                    FStar_Syntax_Print.binders_to_string ", "
                                      uu___7 in
                                  let uu___7 = FStar_Errors_Msg.rendermsg msg in
                                  fail3
                                    "Cannot type (3) %s in context (%s). Error = (%s)"
                                    uu___5 uu___6 uu___7))) uu___))) uu___1
        uu___
let (tcc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu___ =
        let uu___1 = __tc_lax e t in
        Obj.magic
          (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
             (Obj.magic uu___1)
             (fun uu___2 ->
                (fun uu___2 ->
                   let uu___2 = Obj.magic uu___2 in
                   match uu___2 with
                   | (uu___3, lc, uu___4) ->
                       let uu___5 =
                         let uu___6 = FStar_TypeChecker_Common.lcomp_comp lc in
                         FStar_Pervasives_Native.fst uu___6 in
                       Obj.magic
                         (FStar_Class_Monad.return
                            FStar_Tactics_Monad.monad_tac ()
                            (Obj.magic uu___5))) uu___2)) in
      FStar_Tactics_Monad.wrap_err "tcc" uu___
let (tc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu___ =
        let uu___1 = tcc e t in
        Obj.magic
          (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
             (Obj.magic uu___1)
             (fun uu___2 ->
                (fun c ->
                   let c = Obj.magic c in
                   Obj.magic
                     (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                        () (Obj.magic (FStar_Syntax_Util.comp_result c))))
                  uu___2)) in
      FStar_Tactics_Monad.wrap_err "tc" uu___
let rec map :
  'a . 'a FStar_Tactics_Monad.tac -> 'a Prims.list FStar_Tactics_Monad.tac =
  fun uu___ ->
    (fun tau ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            (Obj.magic FStar_Tactics_Monad.get)
            (fun uu___ ->
               (fun ps ->
                  let ps = Obj.magic ps in
                  match ps.FStar_Tactics_Types.goals with
                  | [] ->
                      Obj.magic
                        (FStar_Class_Monad.return
                           FStar_Tactics_Monad.monad_tac () (Obj.magic []))
                  | uu___::uu___1 ->
                      let uu___2 =
                        let uu___3 = map tau in
                        FStar_Tactics_Monad.divide FStar_BigInt.one tau
                          uu___3 in
                      Obj.magic
                        (FStar_Class_Monad.op_let_Bang
                           FStar_Tactics_Monad.monad_tac () ()
                           (Obj.magic uu___2)
                           (fun uu___3 ->
                              (fun uu___3 ->
                                 let uu___3 = Obj.magic uu___3 in
                                 match uu___3 with
                                 | (h, t) ->
                                     Obj.magic
                                       (FStar_Class_Monad.return
                                          FStar_Tactics_Monad.monad_tac ()
                                          (Obj.magic (h :: t)))) uu___3)))
                 uu___))) uu___
let (seq :
  unit FStar_Tactics_Monad.tac ->
    unit FStar_Tactics_Monad.tac -> unit FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let uu___ =
        FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () () t1
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___1 = Obj.magic uu___1 in
                let uu___2 = map t2 in
                Obj.magic
                  (FStar_Class_Monad.op_let_Bang
                     FStar_Tactics_Monad.monad_tac () () (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___3 = Obj.magic uu___3 in
                           Obj.magic
                             (FStar_Class_Monad.return
                                FStar_Tactics_Monad.monad_tac ()
                                (Obj.repr ()))) uu___3))) uu___1) in
      FStar_Tactics_Monad.focus uu___
let (should_check_goal_uvar :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.should_check_uvar) =
  fun g ->
    FStar_Syntax_Util.ctx_uvar_should_check
      g.FStar_Tactics_Types.goal_ctx_uvar
let (bnorm_and_replace :
  FStar_Tactics_Types.goal -> unit FStar_Tactics_Monad.tac) =
  fun g -> let uu___ = bnorm_goal g in FStar_Tactics_Monad.replace_cur uu___
let (bv_to_binding :
  FStar_Syntax_Syntax.bv -> FStar_Reflection_V2_Data.binding) =
  fun bv ->
    let uu___ = FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index in
    let uu___1 =
      let uu___2 =
        FStar_Class_Show.show FStar_Ident.showable_ident
          bv.FStar_Syntax_Syntax.ppname in
      FStar_Compiler_Sealed.seal uu___2 in
    {
      FStar_Reflection_V2_Data.uniq1 = uu___;
      FStar_Reflection_V2_Data.sort3 = (bv.FStar_Syntax_Syntax.sort);
      FStar_Reflection_V2_Data.ppname3 = uu___1
    }
let (binder_to_binding :
  FStar_Syntax_Syntax.binder -> FStar_Reflection_V2_Data.binding) =
  fun b -> bv_to_binding b.FStar_Syntax_Syntax.binder_bv
let (binding_to_string : FStar_Reflection_V2_Data.binding -> Prims.string) =
  fun b ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_BigInt.to_int_fs b.FStar_Reflection_V2_Data.uniq1 in
        FStar_Class_Show.show
          (FStar_Class_Show.printableshow FStar_Class_Printable.printable_int)
          uu___2 in
      Prims.strcat "#" uu___1 in
    Prims.strcat
      (FStar_Compiler_Sealed.unseal b.FStar_Reflection_V2_Data.ppname3) uu___
let (binding_to_bv :
  FStar_Reflection_V2_Data.binding -> FStar_Syntax_Syntax.bv) =
  fun b ->
    let uu___ =
      FStar_Ident.mk_ident
        ((FStar_Compiler_Sealed.unseal b.FStar_Reflection_V2_Data.ppname3),
          FStar_Compiler_Range_Type.dummyRange) in
    let uu___1 = FStar_BigInt.to_int_fs b.FStar_Reflection_V2_Data.uniq1 in
    {
      FStar_Syntax_Syntax.ppname = uu___;
      FStar_Syntax_Syntax.index = uu___1;
      FStar_Syntax_Syntax.sort = (b.FStar_Reflection_V2_Data.sort3)
    }
let (binding_to_binder :
  FStar_Reflection_V2_Data.binding -> FStar_Syntax_Syntax.binder) =
  fun b -> let bv = binding_to_bv b in FStar_Syntax_Syntax.mk_binder bv
let (arrow_one :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.binder *
        FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun t ->
      let uu___ = FStar_Syntax_Util.arrow_one_ln t in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (b, c) ->
          let uu___1 = FStar_TypeChecker_Core.open_binders_in_comp env1 [b] c in
          (match uu___1 with
           | (env2, b1::[], c1) ->
               FStar_Pervasives_Native.Some (env2, b1, c1))
let (arrow_one_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.binder *
        FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun t ->
      let uu___ = arrow_one env1 t in
      match uu___ with
      | FStar_Pervasives_Native.Some r -> FStar_Pervasives_Native.Some r
      | FStar_Pervasives_Native.None ->
          let uu___1 = whnf env1 t in arrow_one env1 uu___1
let (intro :
  unit -> FStar_Reflection_V2_Data.binding FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      Obj.magic
        (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
           (Obj.magic FStar_Tactics_Monad.cur_goal)
           (fun uu___2 ->
              (fun goal ->
                 let goal = Obj.magic goal in
                 let uu___2 =
                   let uu___3 = FStar_Tactics_Types.goal_env goal in
                   let uu___4 = FStar_Tactics_Types.goal_type goal in
                   arrow_one_whnf uu___3 uu___4 in
                 match uu___2 with
                 | FStar_Pervasives_Native.Some (uu___3, uu___4, c) when
                     let uu___5 = FStar_Syntax_Util.is_total_comp c in
                     Prims.op_Negation uu___5 ->
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Monad.fail "Codomain is effectful"))
                 | FStar_Pervasives_Native.Some (env', b, c) ->
                     Obj.magic
                       (Obj.repr
                          (let typ' = FStar_Syntax_Util.comp_result c in
                           let uu___3 =
                             let uu___4 =
                               let uu___5 = should_check_goal_uvar goal in
                               FStar_Pervasives_Native.Some uu___5 in
                             let uu___5 =
                               FStar_Tactics_Monad.goal_typedness_deps goal in
                             FStar_Tactics_Monad.new_uvar "intro" env' typ'
                               uu___4 uu___5 (rangeof goal) in
                           FStar_Class_Monad.op_let_Bang
                             FStar_Tactics_Monad.monad_tac () ()
                             (Obj.magic uu___3)
                             (fun uu___4 ->
                                (fun uu___4 ->
                                   let uu___4 = Obj.magic uu___4 in
                                   match uu___4 with
                                   | (body, ctx_uvar) ->
                                       let sol =
                                         let uu___5 =
                                           let uu___6 =
                                             FStar_Syntax_Util.residual_comp_of_comp
                                               c in
                                           FStar_Pervasives_Native.Some
                                             uu___6 in
                                         FStar_Syntax_Util.abs [b] body
                                           uu___5 in
                                       let uu___5 = set_solution goal sol in
                                       Obj.magic
                                         (FStar_Class_Monad.op_let_Bang
                                            FStar_Tactics_Monad.monad_tac ()
                                            () uu___5
                                            (fun uu___6 ->
                                               (fun uu___6 ->
                                                  let uu___6 =
                                                    Obj.magic uu___6 in
                                                  let g =
                                                    FStar_Tactics_Types.mk_goal
                                                      env' ctx_uvar
                                                      goal.FStar_Tactics_Types.opts
                                                      goal.FStar_Tactics_Types.is_guard
                                                      goal.FStar_Tactics_Types.label in
                                                  let uu___7 =
                                                    bnorm_and_replace g in
                                                  Obj.magic
                                                    (FStar_Class_Monad.op_let_Bang
                                                       FStar_Tactics_Monad.monad_tac
                                                       () () uu___7
                                                       (fun uu___8 ->
                                                          (fun uu___8 ->
                                                             let uu___8 =
                                                               Obj.magic
                                                                 uu___8 in
                                                             let uu___9 =
                                                               binder_to_binding
                                                                 b in
                                                             Obj.magic
                                                               (FStar_Class_Monad.return
                                                                  FStar_Tactics_Monad.monad_tac
                                                                  ()
                                                                  (Obj.magic
                                                                    uu___9)))
                                                            uu___8))) uu___6)))
                                  uu___4)))
                 | FStar_Pervasives_Native.None ->
                     Obj.magic
                       (Obj.repr
                          (let uu___3 =
                             let uu___4 = FStar_Tactics_Types.goal_env goal in
                             let uu___5 = FStar_Tactics_Types.goal_type goal in
                             tts uu___4 uu___5 in
                           fail1 "goal is not an arrow (%s)" uu___3))) uu___2)) in
    FStar_Tactics_Monad.wrap_err "intro" uu___1
let (intro_rec :
  unit ->
    (FStar_Reflection_V2_Data.binding * FStar_Reflection_V2_Data.binding)
      FStar_Tactics_Monad.tac)
  =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            (Obj.magic FStar_Tactics_Monad.cur_goal)
            (fun uu___1 ->
               (fun goal ->
                  let goal = Obj.magic goal in
                  FStar_Compiler_Util.print_string
                    "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
                  FStar_Compiler_Util.print_string
                    "WARNING (intro_rec): proceed at your own risk...\n";
                  (let uu___3 =
                     let uu___4 = FStar_Tactics_Types.goal_env goal in
                     let uu___5 =
                       let uu___6 = FStar_Tactics_Types.goal_env goal in
                       let uu___7 = FStar_Tactics_Types.goal_type goal in
                       whnf uu___6 uu___7 in
                     arrow_one uu___4 uu___5 in
                   match uu___3 with
                   | FStar_Pervasives_Native.Some (env', b, c) ->
                       Obj.magic
                         (Obj.repr
                            (let uu___4 =
                               let uu___5 = FStar_Syntax_Util.is_total_comp c in
                               Prims.op_Negation uu___5 in
                             if uu___4
                             then
                               Obj.repr
                                 (FStar_Tactics_Monad.fail
                                    "Codomain is effectful")
                             else
                               Obj.repr
                                 (let bv =
                                    let uu___6 =
                                      FStar_Tactics_Types.goal_type goal in
                                    FStar_Syntax_Syntax.gen_bv "__recf"
                                      FStar_Pervasives_Native.None uu___6 in
                                  let uu___6 =
                                    let uu___7 =
                                      let uu___8 =
                                        should_check_goal_uvar goal in
                                      FStar_Pervasives_Native.Some uu___8 in
                                    let uu___8 =
                                      FStar_Tactics_Monad.goal_typedness_deps
                                        goal in
                                    FStar_Tactics_Monad.new_uvar "intro_rec"
                                      env' (FStar_Syntax_Util.comp_result c)
                                      uu___7 uu___8 (rangeof goal) in
                                  FStar_Class_Monad.op_let_Bang
                                    FStar_Tactics_Monad.monad_tac () ()
                                    (Obj.magic uu___6)
                                    (fun uu___7 ->
                                       (fun uu___7 ->
                                          let uu___7 = Obj.magic uu___7 in
                                          match uu___7 with
                                          | (u, ctx_uvar_u) ->
                                              let lb =
                                                let uu___8 =
                                                  FStar_Tactics_Types.goal_type
                                                    goal in
                                                let uu___9 =
                                                  FStar_Syntax_Util.abs 
                                                    [b] u
                                                    FStar_Pervasives_Native.None in
                                                FStar_Syntax_Util.mk_letbinding
                                                  (FStar_Pervasives.Inl bv)
                                                  [] uu___8
                                                  FStar_Parser_Const.effect_Tot_lid
                                                  uu___9 []
                                                  FStar_Compiler_Range_Type.dummyRange in
                                              let body =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  bv in
                                              let uu___8 =
                                                FStar_Syntax_Subst.close_let_rec
                                                  [lb] body in
                                              (match uu___8 with
                                               | (lbs, body1) ->
                                                   let tm =
                                                     let uu___9 =
                                                       let uu___10 =
                                                         FStar_Tactics_Types.goal_witness
                                                           goal in
                                                       uu___10.FStar_Syntax_Syntax.pos in
                                                     FStar_Syntax_Syntax.mk
                                                       (FStar_Syntax_Syntax.Tm_let
                                                          {
                                                            FStar_Syntax_Syntax.lbs
                                                              = (true, lbs);
                                                            FStar_Syntax_Syntax.body1
                                                              = body1
                                                          }) uu___9 in
                                                   let uu___9 =
                                                     set_solution goal tm in
                                                   Obj.magic
                                                     (FStar_Class_Monad.op_let_Bang
                                                        FStar_Tactics_Monad.monad_tac
                                                        () () uu___9
                                                        (fun uu___10 ->
                                                           (fun uu___10 ->
                                                              let uu___10 =
                                                                Obj.magic
                                                                  uu___10 in
                                                              let uu___11 =
                                                                bnorm_and_replace
                                                                  {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (goal.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (goal.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (goal.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (goal.FStar_Tactics_Types.label)
                                                                  } in
                                                              Obj.magic
                                                                (FStar_Class_Monad.op_let_Bang
                                                                   FStar_Tactics_Monad.monad_tac
                                                                   () ()
                                                                   uu___11
                                                                   (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    uu___12 in
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    bv in
                                                                    binder_to_binding
                                                                    uu___15 in
                                                                    let uu___15
                                                                    =
                                                                    binder_to_binding
                                                                    b in
                                                                    (uu___14,
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___13)))
                                                                    uu___12)))
                                                             uu___10))))
                                         uu___7))))
                   | FStar_Pervasives_Native.None ->
                       Obj.magic
                         (Obj.repr
                            (let uu___4 =
                               let uu___5 = FStar_Tactics_Types.goal_env goal in
                               let uu___6 =
                                 FStar_Tactics_Types.goal_type goal in
                               tts uu___5 uu___6 in
                             fail1 "intro_rec: goal is not an arrow (%s)"
                               uu___4)))) uu___1))) uu___
let (norm :
  FStar_Pervasives.norm_step Prims.list -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
      (Obj.magic FStar_Tactics_Monad.cur_goal)
      (fun uu___ ->
         (fun goal ->
            let goal = Obj.magic goal in
            let uu___ =
              FStar_Tactics_Monad.if_verbose
                (fun uu___1 ->
                   let uu___2 =
                     let uu___3 = FStar_Tactics_Types.goal_witness goal in
                     FStar_Class_Show.show FStar_Syntax_Print.showable_term
                       uu___3 in
                   FStar_Compiler_Util.print1 "norm: witness = %s\n" uu___2) in
            Obj.magic
              (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                 () uu___
                 (fun uu___1 ->
                    (fun uu___1 ->
                       let uu___1 = Obj.magic uu___1 in
                       let steps =
                         let uu___2 =
                           FStar_TypeChecker_Cfg.translate_norm_steps s in
                         FStar_Compiler_List.op_At
                           [FStar_TypeChecker_Env.Reify;
                           FStar_TypeChecker_Env.UnfoldTac] uu___2 in
                       let t =
                         let uu___2 = FStar_Tactics_Types.goal_env goal in
                         let uu___3 = FStar_Tactics_Types.goal_type goal in
                         normalize steps uu___2 uu___3 in
                       let uu___2 = FStar_Tactics_Monad.goal_with_type goal t in
                       Obj.magic (FStar_Tactics_Monad.replace_cur uu___2))
                      uu___1))) uu___)
let (norm_term_env :
  env ->
    FStar_Pervasives.norm_step Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun s ->
      fun t ->
        let uu___ =
          Obj.magic
            (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
               () (Obj.magic FStar_Tactics_Monad.get)
               (fun uu___1 ->
                  (fun ps ->
                     let ps = Obj.magic ps in
                     let uu___1 =
                       FStar_Tactics_Monad.if_verbose
                         (fun uu___2 ->
                            let uu___3 =
                              FStar_Class_Show.show
                                FStar_Syntax_Print.showable_term t in
                            FStar_Compiler_Util.print1
                              "norm_term_env: t = %s\n" uu___3) in
                     Obj.magic
                       (FStar_Class_Monad.op_let_Bang
                          FStar_Tactics_Monad.monad_tac () () uu___1
                          (fun uu___2 ->
                             (fun uu___2 ->
                                let uu___2 = Obj.magic uu___2 in
                                let uu___3 = __tc_lax e t in
                                Obj.magic
                                  (FStar_Class_Monad.op_let_Bang
                                     FStar_Tactics_Monad.monad_tac () ()
                                     (Obj.magic uu___3)
                                     (fun uu___4 ->
                                        (fun uu___4 ->
                                           let uu___4 = Obj.magic uu___4 in
                                           match uu___4 with
                                           | (t1, uu___5, uu___6) ->
                                               let steps =
                                                 let uu___7 =
                                                   FStar_TypeChecker_Cfg.translate_norm_steps
                                                     s in
                                                 FStar_Compiler_List.op_At
                                                   [FStar_TypeChecker_Env.Reify;
                                                   FStar_TypeChecker_Env.UnfoldTac]
                                                   uu___7 in
                                               let t2 =
                                                 normalize steps
                                                   ps.FStar_Tactics_Types.main_context
                                                   t1 in
                                               let uu___7 =
                                                 FStar_Tactics_Monad.if_verbose
                                                   (fun uu___8 ->
                                                      let uu___9 =
                                                        FStar_Class_Show.show
                                                          FStar_Syntax_Print.showable_term
                                                          t2 in
                                                      FStar_Compiler_Util.print1
                                                        "norm_term_env: t' = %s\n"
                                                        uu___9) in
                                               Obj.magic
                                                 (FStar_Class_Monad.op_let_Bang
                                                    FStar_Tactics_Monad.monad_tac
                                                    () () uu___7
                                                    (fun uu___8 ->
                                                       (fun uu___8 ->
                                                          let uu___8 =
                                                            Obj.magic uu___8 in
                                                          Obj.magic
                                                            (FStar_Class_Monad.return
                                                               FStar_Tactics_Monad.monad_tac
                                                               ()
                                                               (Obj.magic t2)))
                                                         uu___8))) uu___4)))
                               uu___2))) uu___1)) in
        FStar_Tactics_Monad.wrap_err "norm_term" uu___
let (refine_intro : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
        (Obj.magic FStar_Tactics_Monad.cur_goal)
        (fun uu___2 ->
           (fun g ->
              let g = Obj.magic g in
              let uu___2 =
                let uu___3 = FStar_Tactics_Types.goal_env g in
                let uu___4 = FStar_Tactics_Types.goal_type g in
                FStar_TypeChecker_Rel.base_and_refinement uu___3 uu___4 in
              match uu___2 with
              | (uu___3, FStar_Pervasives_Native.None) ->
                  Obj.magic (FStar_Tactics_Monad.fail "not a refinement")
              | (t, FStar_Pervasives_Native.Some (bv, phi)) ->
                  (FStar_Tactics_Monad.mark_goal_implicit_already_checked g;
                   (let g1 = FStar_Tactics_Monad.goal_with_type g t in
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = FStar_Syntax_Syntax.mk_binder bv in
                          [uu___7] in
                        FStar_Syntax_Subst.open_term uu___6 phi in
                      match uu___5 with
                      | (bvs, phi1) ->
                          let uu___6 =
                            let uu___7 = FStar_Compiler_List.hd bvs in
                            uu___7.FStar_Syntax_Syntax.binder_bv in
                          (uu___6, phi1) in
                    match uu___4 with
                    | (bv1, phi1) ->
                        let uu___5 =
                          let uu___6 = FStar_Tactics_Types.goal_env g in
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    FStar_Tactics_Types.goal_witness g in
                                  (bv1, uu___11) in
                                FStar_Syntax_Syntax.NT uu___10 in
                              [uu___9] in
                            FStar_Syntax_Subst.subst uu___8 phi1 in
                          let uu___8 =
                            let uu___9 = should_check_goal_uvar g in
                            FStar_Pervasives_Native.Some uu___9 in
                          FStar_Tactics_Monad.mk_irrelevant_goal
                            "refine_intro refinement" uu___6 uu___7 uu___8
                            (rangeof g) g.FStar_Tactics_Types.opts
                            g.FStar_Tactics_Types.label in
                        Obj.magic
                          (FStar_Class_Monad.op_let_Bang
                             FStar_Tactics_Monad.monad_tac () ()
                             (Obj.magic uu___5)
                             (fun uu___6 ->
                                (fun g2 ->
                                   let g2 = Obj.magic g2 in
                                   Obj.magic
                                     (FStar_Class_Monad.op_let_Bang
                                        FStar_Tactics_Monad.monad_tac () ()
                                        FStar_Tactics_Monad.dismiss
                                        (fun uu___6 ->
                                           (fun uu___6 ->
                                              let uu___6 = Obj.magic uu___6 in
                                              Obj.magic
                                                (FStar_Tactics_Monad.add_goals
                                                   [g1; g2])) uu___6)))
                                  uu___6))))) uu___2) in
    FStar_Tactics_Monad.wrap_err "refine_intro" uu___1
let (__exact_now :
  Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun set_expected_typ ->
    fun t ->
      FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
        (Obj.magic FStar_Tactics_Monad.cur_goal)
        (fun uu___ ->
           (fun goal ->
              let goal = Obj.magic goal in
              let env1 =
                if set_expected_typ
                then
                  let uu___ = FStar_Tactics_Types.goal_env goal in
                  let uu___1 = FStar_Tactics_Types.goal_type goal in
                  FStar_TypeChecker_Env.set_expected_typ uu___ uu___1
                else FStar_Tactics_Types.goal_env goal in
              let uu___ = __tc env1 t in
              Obj.magic
                (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac
                   () () (Obj.magic uu___)
                   (fun uu___1 ->
                      (fun uu___1 ->
                         let uu___1 = Obj.magic uu___1 in
                         match uu___1 with
                         | (t1, typ, guard) ->
                             let uu___2 =
                               FStar_Tactics_Monad.if_verbose
                                 (fun uu___3 ->
                                    let uu___4 =
                                      FStar_Class_Show.show
                                        FStar_Syntax_Print.showable_term typ in
                                    let uu___5 =
                                      let uu___6 =
                                        FStar_Tactics_Types.goal_env goal in
                                      FStar_TypeChecker_Rel.guard_to_string
                                        uu___6 guard in
                                    FStar_Compiler_Util.print2
                                      "__exact_now: got type %s\n__exact_now: and guard %s\n"
                                      uu___4 uu___5) in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  FStar_Tactics_Monad.monad_tac () () uu___2
                                  (fun uu___3 ->
                                     (fun uu___3 ->
                                        let uu___3 = Obj.magic uu___3 in
                                        let uu___4 =
                                          let uu___5 =
                                            FStar_Tactics_Types.goal_env goal in
                                          let uu___6 =
                                            let uu___7 =
                                              should_check_goal_uvar goal in
                                            FStar_Pervasives_Native.Some
                                              uu___7 in
                                          proc_guard "__exact typing" uu___5
                                            guard uu___6 (rangeof goal) in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             FStar_Tactics_Monad.monad_tac ()
                                             () uu___4
                                             (fun uu___5 ->
                                                (fun uu___5 ->
                                                   let uu___5 =
                                                     Obj.magic uu___5 in
                                                   let uu___6 =
                                                     FStar_Tactics_Monad.if_verbose
                                                       (fun uu___7 ->
                                                          let uu___8 =
                                                            FStar_Class_Show.show
                                                              FStar_Syntax_Print.showable_term
                                                              typ in
                                                          let uu___9 =
                                                            let uu___10 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal in
                                                            FStar_Class_Show.show
                                                              FStar_Syntax_Print.showable_term
                                                              uu___10 in
                                                          FStar_Compiler_Util.print2
                                                            "__exact_now: unifying %s and %s\n"
                                                            uu___8 uu___9) in
                                                   Obj.magic
                                                     (FStar_Class_Monad.op_let_Bang
                                                        FStar_Tactics_Monad.monad_tac
                                                        () () uu___6
                                                        (fun uu___7 ->
                                                           (fun uu___7 ->
                                                              let uu___7 =
                                                                Obj.magic
                                                                  uu___7 in
                                                              let uu___8 =
                                                                let uu___9 =
                                                                  FStar_Tactics_Types.goal_env
                                                                    goal in
                                                                let uu___10 =
                                                                  FStar_Tactics_Types.goal_type
                                                                    goal in
                                                                do_unify true
                                                                  uu___9 typ
                                                                  uu___10 in
                                                              Obj.magic
                                                                (FStar_Class_Monad.op_let_Bang
                                                                   FStar_Tactics_Monad.monad_tac
                                                                   () ()
                                                                   (Obj.magic
                                                                    uu___8)
                                                                   (fun
                                                                    uu___9 ->
                                                                    (fun b ->
                                                                    let b =
                                                                    Obj.magic
                                                                    b in
                                                                    if b
                                                                    then
                                                                    (FStar_Tactics_Monad.mark_goal_implicit_already_checked
                                                                    goal;
                                                                    Obj.magic
                                                                    (solve
                                                                    goal t1))
                                                                    else
                                                                    (let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal in
                                                                    tts
                                                                    uu___12 in
                                                                    let uu___12
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    goal in
                                                                    FStar_TypeChecker_Err.print_discrepancy
                                                                    uu___11
                                                                    typ
                                                                    uu___12 in
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (typ1,
                                                                    goalt) ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal in
                                                                    tts
                                                                    uu___12
                                                                    t1 in
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal in
                                                                    let uu___14
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    goal in
                                                                    tts
                                                                    uu___13
                                                                    uu___14 in
                                                                    Obj.magic
                                                                    (fail4
                                                                    "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                                    uu___11
                                                                    typ1
                                                                    goalt
                                                                    uu___12)))
                                                                    uu___9)))
                                                             uu___7))) uu___5)))
                                       uu___3))) uu___1))) uu___)
let (t_exact :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun try_refine ->
    fun set_expected_typ ->
      fun tm ->
        let uu___ =
          let uu___1 =
            FStar_Tactics_Monad.if_verbose
              (fun uu___2 ->
                 let uu___3 =
                   FStar_Class_Show.show FStar_Syntax_Print.showable_term tm in
                 FStar_Compiler_Util.print1 "t_exact: tm = %s\n" uu___3) in
          FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            uu___1
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___2 = Obj.magic uu___2 in
                  let uu___3 =
                    let uu___4 = __exact_now set_expected_typ tm in
                    FStar_Tactics_Monad.catch uu___4 in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang
                       FStar_Tactics_Monad.monad_tac () () (Obj.magic uu___3)
                       (fun uu___4 ->
                          (fun uu___4 ->
                             let uu___4 = Obj.magic uu___4 in
                             match uu___4 with
                             | FStar_Pervasives.Inr r ->
                                 Obj.magic
                                   (FStar_Class_Monad.return
                                      FStar_Tactics_Monad.monad_tac ()
                                      (Obj.repr ()))
                             | FStar_Pervasives.Inl e when
                                 Prims.op_Negation try_refine ->
                                 Obj.magic (FStar_Tactics_Monad.traise e)
                             | FStar_Pervasives.Inl e ->
                                 let uu___5 =
                                   FStar_Tactics_Monad.if_verbose
                                     (fun uu___6 ->
                                        FStar_Compiler_Util.print_string
                                          "__exact_now failed, trying refine...\n") in
                                 Obj.magic
                                   (FStar_Class_Monad.op_let_Bang
                                      FStar_Tactics_Monad.monad_tac () ()
                                      uu___5
                                      (fun uu___6 ->
                                         (fun uu___6 ->
                                            let uu___6 = Obj.magic uu___6 in
                                            let uu___7 =
                                              let uu___8 =
                                                let uu___9 =
                                                  norm
                                                    [FStar_Pervasives.Delta] in
                                                FStar_Class_Monad.op_let_Bang
                                                  FStar_Tactics_Monad.monad_tac
                                                  () () uu___9
                                                  (fun uu___10 ->
                                                     (fun uu___10 ->
                                                        let uu___10 =
                                                          Obj.magic uu___10 in
                                                        let uu___11 =
                                                          refine_intro () in
                                                        Obj.magic
                                                          (FStar_Class_Monad.op_let_Bang
                                                             FStar_Tactics_Monad.monad_tac
                                                             () () uu___11
                                                             (fun uu___12 ->
                                                                (fun uu___12
                                                                   ->
                                                                   let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    uu___12 in
                                                                   Obj.magic
                                                                    (__exact_now
                                                                    set_expected_typ
                                                                    tm))
                                                                  uu___12)))
                                                       uu___10) in
                                              FStar_Tactics_Monad.catch
                                                uu___8 in
                                            Obj.magic
                                              (FStar_Class_Monad.op_let_Bang
                                                 FStar_Tactics_Monad.monad_tac
                                                 () () (Obj.magic uu___7)
                                                 (fun uu___8 ->
                                                    (fun uu___8 ->
                                                       let uu___8 =
                                                         Obj.magic uu___8 in
                                                       match uu___8 with
                                                       | FStar_Pervasives.Inr
                                                           r ->
                                                           let uu___9 =
                                                             FStar_Tactics_Monad.if_verbose
                                                               (fun uu___10
                                                                  ->
                                                                  FStar_Compiler_Util.print_string
                                                                    "__exact_now: failed after refining too\n") in
                                                           Obj.magic
                                                             (FStar_Class_Monad.op_let_Bang
                                                                FStar_Tactics_Monad.monad_tac
                                                                () () uu___9
                                                                (fun uu___10
                                                                   ->
                                                                   (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    uu___10 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.repr
                                                                    ())))
                                                                    uu___10))
                                                       | FStar_Pervasives.Inl
                                                           uu___9 ->
                                                           let uu___10 =
                                                             FStar_Tactics_Monad.if_verbose
                                                               (fun uu___11
                                                                  ->
                                                                  FStar_Compiler_Util.print_string
                                                                    "__exact_now: was not a refinement\n") in
                                                           Obj.magic
                                                             (FStar_Class_Monad.op_let_Bang
                                                                FStar_Tactics_Monad.monad_tac
                                                                () () uu___10
                                                                (fun uu___11
                                                                   ->
                                                                   (fun
                                                                    uu___11
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    uu___11 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Monad.traise
                                                                    e))
                                                                    uu___11)))
                                                      uu___8))) uu___6)))
                            uu___4))) uu___2) in
        FStar_Tactics_Monad.wrap_err "exact" uu___
let (try_unify_by_application :
  FStar_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option ->
    Prims.bool ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Compiler_Range_Type.range ->
              (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
                FStar_Syntax_Syntax.ctx_uvar) Prims.list
                FStar_Tactics_Monad.tac)
  =
  fun should_check ->
    fun only_match ->
      fun e ->
        fun ty1 ->
          fun ty2 ->
            fun rng ->
              let f = if only_match then do_match else do_unify in
              let must_tot = true in
              let rec aux uu___2 uu___1 uu___ =
                (fun acc ->
                   fun typedness_deps ->
                     fun ty11 ->
                       let uu___ = f must_tot e ty2 ty11 in
                       Obj.magic
                         (FStar_Class_Monad.op_let_Bang
                            FStar_Tactics_Monad.monad_tac () ()
                            (Obj.magic uu___)
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  let uu___1 = Obj.magic uu___1 in
                                  if uu___1
                                  then
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Class_Monad.return
                                            FStar_Tactics_Monad.monad_tac ()
                                            (Obj.magic acc)))
                                  else
                                    Obj.magic
                                      (Obj.repr
                                         (let uu___2 =
                                            FStar_Syntax_Util.arrow_one ty11 in
                                          match uu___2 with
                                          | FStar_Pervasives_Native.None ->
                                              Obj.repr
                                                (let uu___3 = tts e ty11 in
                                                 let uu___4 = tts e ty2 in
                                                 fail2
                                                   "Could not instantiate, %s to %s"
                                                   uu___3 uu___4)
                                          | FStar_Pervasives_Native.Some
                                              (b, c) ->
                                              Obj.repr
                                                (let uu___3 =
                                                   let uu___4 =
                                                     FStar_Syntax_Util.is_total_comp
                                                       c in
                                                   Prims.op_Negation uu___4 in
                                                 if uu___3
                                                 then
                                                   Obj.repr
                                                     (FStar_Tactics_Monad.fail
                                                        "Codomain is effectful")
                                                 else
                                                   Obj.repr
                                                     (let uu___5 =
                                                        FStar_Tactics_Monad.new_uvar
                                                          "apply arg" e
                                                          (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                                          should_check
                                                          typedness_deps rng in
                                                      FStar_Class_Monad.op_let_Bang
                                                        FStar_Tactics_Monad.monad_tac
                                                        () ()
                                                        (Obj.magic uu___5)
                                                        (fun uu___6 ->
                                                           (fun uu___6 ->
                                                              let uu___6 =
                                                                Obj.magic
                                                                  uu___6 in
                                                              match uu___6
                                                              with
                                                              | (uvt, uv) ->
                                                                  let uu___7
                                                                    =
                                                                    FStar_Tactics_Monad.if_verbose
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_Class_Show.show
                                                                    FStar_Syntax_Print.showable_ctxu
                                                                    uv in
                                                                    FStar_Compiler_Util.print1
                                                                    "t_apply: generated uvar %s\n"
                                                                    uu___9) in
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___7
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    uu___8 in
                                                                    let typ =
                                                                    FStar_Syntax_Util.comp_result
                                                                    c in
                                                                    let typ'
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    [
                                                                    FStar_Syntax_Syntax.NT
                                                                    ((b.FStar_Syntax_Syntax.binder_bv),
                                                                    uvt)] typ in
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStar_Syntax_Util.aqual_of_binder
                                                                    b in
                                                                    (uvt,
                                                                    uu___11,
                                                                    uv) in
                                                                    uu___10
                                                                    :: acc in
                                                                    Obj.magic
                                                                    (aux
                                                                    uu___9
                                                                    (uv ::
                                                                    typedness_deps)
                                                                    typ'))
                                                                    uu___8)))
                                                             uu___6))))))
                                 uu___1))) uu___2 uu___1 uu___ in
              aux [] [] ty1
let (apply_implicits_as_goals :
  FStar_TypeChecker_Env.env ->
    FStar_Tactics_Types.goal FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
        FStar_Tactics_Types.goal Prims.list Prims.list
          FStar_Tactics_Monad.tac)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun env1 ->
           fun gl ->
             fun imps ->
               let one_implicit_as_goal uu___ =
                 (fun uu___ ->
                    match uu___ with
                    | (term, ctx_uvar) ->
                        let uu___1 = FStar_Syntax_Util.head_and_args term in
                        (match uu___1 with
                         | (hd, uu___2) ->
                             let uu___3 =
                               let uu___4 = FStar_Syntax_Subst.compress hd in
                               uu___4.FStar_Syntax_Syntax.n in
                             (match uu___3 with
                              | FStar_Syntax_Syntax.Tm_uvar
                                  (ctx_uvar1, uu___4) ->
                                  let gl1 =
                                    match gl with
                                    | FStar_Pervasives_Native.None ->
                                        let uu___5 = FStar_Options.peek () in
                                        FStar_Tactics_Types.mk_goal env1
                                          ctx_uvar1 uu___5 true
                                          "goal for unsolved implicit"
                                    | FStar_Pervasives_Native.Some gl2 ->
                                        {
                                          FStar_Tactics_Types.goal_main_env =
                                            (gl2.FStar_Tactics_Types.goal_main_env);
                                          FStar_Tactics_Types.goal_ctx_uvar =
                                            ctx_uvar1;
                                          FStar_Tactics_Types.opts =
                                            (gl2.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (gl2.FStar_Tactics_Types.is_guard);
                                          FStar_Tactics_Types.label =
                                            (gl2.FStar_Tactics_Types.label)
                                        } in
                                  let gl2 = bnorm_goal gl1 in
                                  Obj.magic
                                    (FStar_Class_Monad.return
                                       FStar_Tactics_Monad.monad_tac ()
                                       (Obj.magic [gl2]))
                              | uu___4 ->
                                  Obj.magic
                                    (FStar_Class_Monad.return
                                       FStar_Tactics_Monad.monad_tac ()
                                       (Obj.magic []))))) uu___ in
               Obj.magic
                 (FStar_Class_Monad.mapM FStar_Tactics_Monad.monad_tac () ()
                    (fun uu___ -> (Obj.magic one_implicit_as_goal) uu___)
                    (Obj.magic imps))) uu___2 uu___1 uu___
let (t_apply :
  Prims.bool ->
    Prims.bool ->
      Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun uopt ->
    fun only_match ->
      fun tc_resolved_uvars ->
        fun tm ->
          let uu___ =
            let tc_resolved_uvars1 = true in
            let uu___1 =
              FStar_Tactics_Monad.if_verbose
                (fun uu___2 ->
                   let uu___3 =
                     FStar_Class_Show.show
                       (FStar_Class_Show.printableshow
                          FStar_Class_Printable.printable_bool) uopt in
                   let uu___4 =
                     FStar_Class_Show.show
                       (FStar_Class_Show.printableshow
                          FStar_Class_Printable.printable_bool) only_match in
                   let uu___5 =
                     FStar_Class_Show.show
                       (FStar_Class_Show.printableshow
                          FStar_Class_Printable.printable_bool)
                       tc_resolved_uvars1 in
                   let uu___6 =
                     FStar_Class_Show.show FStar_Syntax_Print.showable_term
                       tm in
                   FStar_Compiler_Util.print4
                     "t_apply: uopt %s, only_match %s, tc_resolved_uvars %s, tm = %s\n"
                     uu___3 uu___4 uu___5 uu___6) in
            FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
              uu___1
              (fun uu___2 ->
                 (fun uu___2 ->
                    let uu___2 = Obj.magic uu___2 in
                    Obj.magic
                      (FStar_Class_Monad.op_let_Bang
                         FStar_Tactics_Monad.monad_tac () ()
                         (Obj.magic FStar_Tactics_Monad.get)
                         (fun uu___3 ->
                            (fun ps ->
                               let ps = Obj.magic ps in
                               Obj.magic
                                 (FStar_Class_Monad.op_let_Bang
                                    FStar_Tactics_Monad.monad_tac () ()
                                    (Obj.magic FStar_Tactics_Monad.cur_goal)
                                    (fun uu___3 ->
                                       (fun goal ->
                                          let goal = Obj.magic goal in
                                          let e =
                                            FStar_Tactics_Types.goal_env goal in
                                          let should_check =
                                            should_check_goal_uvar goal in
                                          FStar_Tactics_Monad.register_goal
                                            goal;
                                          (let uu___4 = __tc e tm in
                                           Obj.magic
                                             (FStar_Class_Monad.op_let_Bang
                                                FStar_Tactics_Monad.monad_tac
                                                () () (Obj.magic uu___4)
                                                (fun uu___5 ->
                                                   (fun uu___5 ->
                                                      let uu___5 =
                                                        Obj.magic uu___5 in
                                                      match uu___5 with
                                                      | (tm1, typ, guard) ->
                                                          let uu___6 =
                                                            FStar_Tactics_Monad.if_verbose
                                                              (fun uu___7 ->
                                                                 let uu___8 =
                                                                   FStar_Class_Show.show
                                                                    FStar_Syntax_Print.showable_term
                                                                    tm1 in
                                                                 let uu___9 =
                                                                   FStar_Tactics_Printing.goal_to_string_verbose
                                                                    goal in
                                                                 let uu___10
                                                                   =
                                                                   FStar_Class_Show.show
                                                                    (FStar_Class_Show.show_list
                                                                    FStar_Syntax_Print.showable_binding)
                                                                    e.FStar_TypeChecker_Env.gamma in
                                                                 let uu___11
                                                                   =
                                                                   FStar_Class_Show.show
                                                                    FStar_Syntax_Print.showable_term
                                                                    typ in
                                                                 let uu___12
                                                                   =
                                                                   FStar_TypeChecker_Rel.guard_to_string
                                                                    e guard in
                                                                 FStar_Compiler_Util.print5
                                                                   "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\ntyp=%s\nguard=%s\n"
                                                                   uu___8
                                                                   uu___9
                                                                   uu___10
                                                                   uu___11
                                                                   uu___12) in
                                                          Obj.magic
                                                            (FStar_Class_Monad.op_let_Bang
                                                               FStar_Tactics_Monad.monad_tac
                                                               () () uu___6
                                                               (fun uu___7 ->
                                                                  (fun uu___7
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    uu___7 in
                                                                    let typ1
                                                                    =
                                                                    bnorm e
                                                                    typ in
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    only_match
                                                                    &&
                                                                    (let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStar_Syntax_Free.uvars_uncached
                                                                    typ1 in
                                                                    FStar_Compiler_Set.is_empty
                                                                    FStar_Syntax_Free.ord_ctx_uvar
                                                                    uu___11 in
                                                                    Prims.op_Negation
                                                                    uu___10) in
                                                                    if uu___9
                                                                    then
                                                                    FStar_Tactics_Monad.fail
                                                                    "t_apply: only_match is on, but the type of the term to apply is not a uvar"
                                                                    else
                                                                    FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.repr
                                                                    ()) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___8
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    uu___9 in
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    goal in
                                                                    try_unify_by_application
                                                                    (FStar_Pervasives_Native.Some
                                                                    should_check)
                                                                    only_match
                                                                    e typ1
                                                                    uu___11
                                                                    (rangeof
                                                                    goal) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun uvs
                                                                    ->
                                                                    let uvs =
                                                                    Obj.magic
                                                                    uvs in
                                                                    let uu___11
                                                                    =
                                                                    FStar_Tactics_Monad.if_verbose
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    (FStar_Common.string_of_list
                                                                    ())
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    (t,
                                                                    uu___15,
                                                                    uu___16)
                                                                    ->
                                                                    FStar_Class_Show.show
                                                                    FStar_Syntax_Print.showable_term
                                                                    t) uvs in
                                                                    FStar_Compiler_Util.print1
                                                                    "t_apply: found args = %s\n"
                                                                    uu___13) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___11
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    uu___12 in
                                                                    let w =
                                                                    FStar_Compiler_List.fold_right
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    fun w1 ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    (uvt, q,
                                                                    uu___14)
                                                                    ->
                                                                    FStar_Syntax_Util.mk_app
                                                                    w1
                                                                    [
                                                                    (uvt, q)])
                                                                    uvs tm1 in
                                                                    let uvset
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    FStar_Syntax_Free.new_uv_set
                                                                    () in
                                                                    FStar_Compiler_List.fold_right
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    fun s ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    (uu___15,
                                                                    uu___16,
                                                                    uv) ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStar_Syntax_Util.ctx_uvar_typ
                                                                    uv in
                                                                    FStar_Syntax_Free.uvars
                                                                    uu___18 in
                                                                    FStar_Compiler_Set.union
                                                                    FStar_Syntax_Free.ord_ctx_uvar
                                                                    s uu___17)
                                                                    uvs
                                                                    uu___13 in
                                                                    let free_in_some_goal
                                                                    uv =
                                                                    FStar_Compiler_Set.mem
                                                                    FStar_Syntax_Free.ord_ctx_uvar
                                                                    uv uvset in
                                                                    let uu___13
                                                                    =
                                                                    solve'
                                                                    goal w in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___13
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    uu___14 in
                                                                    let uvt_uv_l
                                                                    =
                                                                    FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    (uvt, _q,
                                                                    uv) ->
                                                                    (uvt, uv))
                                                                    uvs in
                                                                    let uu___15
                                                                    =
                                                                    apply_implicits_as_goals
                                                                    e
                                                                    (FStar_Pervasives_Native.Some
                                                                    goal)
                                                                    uvt_uv_l in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    sub_goals
                                                                    ->
                                                                    let sub_goals
                                                                    =
                                                                    Obj.magic
                                                                    sub_goals in
                                                                    let sub_goals1
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStar_Compiler_List.filter
                                                                    (fun g ->
                                                                    let uu___18
                                                                    =
                                                                    uopt &&
                                                                    (free_in_some_goal
                                                                    g.FStar_Tactics_Types.goal_ctx_uvar) in
                                                                    Prims.op_Negation
                                                                    uu___18)
                                                                    (FStar_Compiler_List.flatten
                                                                    sub_goals) in
                                                                    FStar_Compiler_List.map
                                                                    bnorm_goal
                                                                    uu___17 in
                                                                    FStar_Compiler_List.rev
                                                                    uu___16 in
                                                                    let uu___16
                                                                    =
                                                                    FStar_Tactics_Monad.add_goals
                                                                    sub_goals1 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___16
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    Obj.magic
                                                                    uu___17 in
                                                                    Obj.magic
                                                                    (proc_guard
                                                                    "apply guard"
                                                                    e guard
                                                                    (FStar_Pervasives_Native.Some
                                                                    should_check)
                                                                    (rangeof
                                                                    goal)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___9)))
                                                                    uu___7)))
                                                     uu___5)))) uu___3)))
                              uu___3))) uu___2) in
          FStar_Tactics_Monad.wrap_err "apply" uu___
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c ->
    let uu___ = FStar_Syntax_Util.comp_eff_name_res_and_args c in
    match uu___ with
    | (eff_name, res, args) ->
        let uu___1 =
          FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Lemma_lid in
        if uu___1
        then
          let uu___2 =
            match args with
            | pre::post::uu___3 ->
                ((FStar_Pervasives_Native.fst pre),
                  (FStar_Pervasives_Native.fst post))
            | uu___3 ->
                FStar_Compiler_Effect.failwith
                  "apply_lemma: impossible: not a lemma" in
          (match uu___2 with
           | (pre, post) ->
               let post1 =
                 let uu___3 =
                   let uu___4 =
                     FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
                   [uu___4] in
                 FStar_Syntax_Util.mk_app post uu___3 in
               FStar_Pervasives_Native.Some (pre, post1))
        else
          (let uu___3 =
             (FStar_Syntax_Util.is_pure_effect eff_name) ||
               (FStar_Syntax_Util.is_ghost_effect eff_name) in
           if uu___3
           then
             let uu___4 = FStar_Syntax_Util.un_squash res in
             FStar_Compiler_Util.map_opt uu___4
               (fun post -> (FStar_Syntax_Util.t_true, post))
           else FStar_Pervasives_Native.None)
let (t_apply_lemma :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun noinst ->
    fun noinst_lhs ->
      fun tm ->
        let uu___ =
          let uu___1 =
            FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
              (Obj.magic FStar_Tactics_Monad.get)
              (fun uu___2 ->
                 (fun ps ->
                    let ps = Obj.magic ps in
                    let uu___2 =
                      FStar_Tactics_Monad.if_verbose
                        (fun uu___3 ->
                           let uu___4 =
                             FStar_Class_Show.show
                               FStar_Syntax_Print.showable_term tm in
                           FStar_Compiler_Util.print1
                             "apply_lemma: tm = %s\n" uu___4) in
                    Obj.magic
                      (FStar_Class_Monad.op_let_Bang
                         FStar_Tactics_Monad.monad_tac () () uu___2
                         (fun uu___3 ->
                            (fun uu___3 ->
                               let uu___3 = Obj.magic uu___3 in
                               let is_unit_t t =
                                 let uu___4 =
                                   let uu___5 = FStar_Syntax_Subst.compress t in
                                   uu___5.FStar_Syntax_Syntax.n in
                                 match uu___4 with
                                 | FStar_Syntax_Syntax.Tm_fvar fv when
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.unit_lid
                                     -> true
                                 | uu___5 -> false in
                               Obj.magic
                                 (FStar_Class_Monad.op_let_Bang
                                    FStar_Tactics_Monad.monad_tac () ()
                                    (Obj.magic FStar_Tactics_Monad.cur_goal)
                                    (fun uu___4 ->
                                       (fun goal ->
                                          let goal = Obj.magic goal in
                                          let env1 =
                                            FStar_Tactics_Types.goal_env goal in
                                          FStar_Tactics_Monad.register_goal
                                            goal;
                                          (let uu___5 = __tc env1 tm in
                                           Obj.magic
                                             (FStar_Class_Monad.op_let_Bang
                                                FStar_Tactics_Monad.monad_tac
                                                () () (Obj.magic uu___5)
                                                (fun uu___6 ->
                                                   (fun uu___6 ->
                                                      let uu___6 =
                                                        Obj.magic uu___6 in
                                                      match uu___6 with
                                                      | (tm1, t, guard) ->
                                                          let uu___7 =
                                                            FStar_Syntax_Util.arrow_formals_comp
                                                              t in
                                                          (match uu___7 with
                                                           | (bs, comp) ->
                                                               let uu___8 =
                                                                 lemma_or_sq
                                                                   comp in
                                                               (match uu___8
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Monad.fail
                                                                    "not a lemma or squashed function")
                                                                | FStar_Pervasives_Native.Some
                                                                    (pre,
                                                                    post) ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.foldM_left
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    uu___10 in
                                                                    fun
                                                                    uu___11
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    uu___11 in
                                                                    match 
                                                                    (uu___10,
                                                                    uu___11)
                                                                    with
                                                                    | 
                                                                    ((uvs,
                                                                    deps,
                                                                    imps,
                                                                    subst),
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = b;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = aq;
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    = uu___12;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___13;_})
                                                                    ->
                                                                    let b_t =
                                                                    FStar_Syntax_Subst.subst
                                                                    subst
                                                                    b.FStar_Syntax_Syntax.sort in
                                                                    let uu___14
                                                                    =
                                                                    is_unit_t
                                                                    b_t in
                                                                    if
                                                                    uu___14
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    (((FStar_Syntax_Util.exp_unit,
                                                                    aq) ::
                                                                    uvs),
                                                                    deps,
                                                                    imps,
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b,
                                                                    FStar_Syntax_Util.exp_unit))
                                                                    ::
                                                                    subst))))
                                                                    else
                                                                    (let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    should_check_goal_uvar
                                                                    goal in
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Strict
                                                                    ->
                                                                    FStar_Syntax_Syntax.Allow_ghost
                                                                    "apply lemma uvar"
                                                                    | 
                                                                    x -> x in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___18 in
                                                                    FStar_Tactics_Monad.new_uvar
                                                                    "apply_lemma"
                                                                    env1 b_t
                                                                    uu___17
                                                                    deps
                                                                    (rangeof
                                                                    goal) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    Obj.magic
                                                                    uu___17 in
                                                                    match uu___17
                                                                    with
                                                                    | 
                                                                    (t1, u)
                                                                    ->
                                                                    ((
                                                                    let uu___19
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env1
                                                                    (FStar_Options.Other
                                                                    "2635") in
                                                                    if
                                                                    uu___19
                                                                    then
                                                                    let uu___20
                                                                    =
                                                                    FStar_Class_Show.show
                                                                    FStar_Syntax_Print.showable_ctxu
                                                                    u in
                                                                    let uu___21
                                                                    =
                                                                    FStar_Class_Show.show
                                                                    FStar_Syntax_Print.showable_term
                                                                    tm1 in
                                                                    FStar_Compiler_Util.print2
                                                                    "Apply lemma created a new uvar %s while applying %s\n"
                                                                    uu___20
                                                                    uu___21
                                                                    else ());
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    (((t1,
                                                                    aq) ::
                                                                    uvs), (u
                                                                    :: deps),
                                                                    ((t1, u)
                                                                    :: imps),
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b, t1))
                                                                    ::
                                                                    subst))))))
                                                                    uu___17))))
                                                                    uu___11
                                                                    uu___10)
                                                                    (Obj.magic
                                                                    ([], [],
                                                                    [], []))
                                                                    (Obj.magic
                                                                    bs)) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    uu___10 in
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (uvs,
                                                                    uu___11,
                                                                    implicits1,
                                                                    subst) ->
                                                                    let implicits2
                                                                    =
                                                                    FStar_Compiler_List.rev
                                                                    implicits1 in
                                                                    let uvs1
                                                                    =
                                                                    FStar_Compiler_List.rev
                                                                    uvs in
                                                                    let pre1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    subst pre in
                                                                    let post1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    subst
                                                                    post in
                                                                    let post_u
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1
                                                                    post1 in
                                                                    let cmp_func
                                                                    =
                                                                    if noinst
                                                                    then
                                                                    do_match
                                                                    else
                                                                    if
                                                                    noinst_lhs
                                                                    then
                                                                    do_match_on_lhs
                                                                    else
                                                                    do_unify in
                                                                    let uu___12
                                                                    =
                                                                    let must_tot
                                                                    = false in
                                                                    let uu___13
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    goal in
                                                                    let uu___14
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    post_u
                                                                    post1 in
                                                                    cmp_func
                                                                    must_tot
                                                                    env1
                                                                    uu___13
                                                                    uu___14 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun b ->
                                                                    let b =
                                                                    Obj.magic
                                                                    b in
                                                                    if
                                                                    Prims.op_Negation
                                                                    b
                                                                    then
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    post_u
                                                                    post1 in
                                                                    let uu___15
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    goal in
                                                                    FStar_TypeChecker_Err.print_discrepancy
                                                                    (tts env1)
                                                                    uu___14
                                                                    uu___15 in
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    (post2,
                                                                    goalt) ->
                                                                    let uu___14
                                                                    =
                                                                    tts env1
                                                                    tm1 in
                                                                    Obj.magic
                                                                    (fail3
                                                                    "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                    uu___14
                                                                    post2
                                                                    goalt)
                                                                    else
                                                                    (let goal_sc
                                                                    =
                                                                    should_check_goal_uvar
                                                                    goal in
                                                                    let uu___14
                                                                    =
                                                                    solve'
                                                                    goal
                                                                    FStar_Syntax_Util.exp_unit in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___14
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    Obj.magic
                                                                    uu___15 in
                                                                    let is_free_uvar
                                                                    uv t1 =
                                                                    let uu___16
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1 in
                                                                    FStar_Compiler_Set.for_any
                                                                    FStar_Syntax_Free.ord_ctx_uvar
                                                                    (fun u ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    uv)
                                                                    uu___16 in
                                                                    let appears
                                                                    uv goals
                                                                    =
                                                                    FStar_Compiler_List.existsML
                                                                    (fun g'
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g' in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu___16)
                                                                    goals in
                                                                    let checkone
                                                                    t1 goals
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1 in
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu___17)
                                                                    ->
                                                                    (match 
                                                                    hd.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,
                                                                    uu___18)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu___18
                                                                    -> false) in
                                                                    let must_tot
                                                                    = false in
                                                                    let uu___16
                                                                    =
                                                                    apply_implicits_as_goals
                                                                    env1
                                                                    (FStar_Pervasives_Native.Some
                                                                    goal)
                                                                    implicits2 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    sub_goals
                                                                    ->
                                                                    let sub_goals
                                                                    =
                                                                    Obj.magic
                                                                    sub_goals in
                                                                    let sub_goals1
                                                                    =
                                                                    FStar_Compiler_List.flatten
                                                                    sub_goals in
                                                                    let rec filter'
                                                                    f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu___17
                                                                    = f x xs1 in
                                                                    if
                                                                    uu___17
                                                                    then
                                                                    let uu___18
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu___18
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g ->
                                                                    fun goals
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g in
                                                                    checkone
                                                                    uu___18
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu___17)
                                                                    sub_goals1 in
                                                                    let uu___17
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    env1
                                                                    guard
                                                                    (FStar_Pervasives_Native.Some
                                                                    goal_sc)
                                                                    (rangeof
                                                                    goal) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___17
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    Obj.magic
                                                                    uu___18 in
                                                                    let pre_u
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 pre1 in
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStar_TypeChecker_Common.NonTrivial
                                                                    pre1) in
                                                                    FStar_TypeChecker_Rel.simplify_guard
                                                                    env1
                                                                    uu___22 in
                                                                    uu___21.FStar_TypeChecker_Common.guard_f in
                                                                    match uu___20
                                                                    with
                                                                    | 
                                                                    FStar_TypeChecker_Common.Trivial
                                                                    ->
                                                                    FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.repr
                                                                    ())
                                                                    | 
                                                                    FStar_TypeChecker_Common.NonTrivial
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Monad.add_irrelevant_goal
                                                                    goal
                                                                    "apply_lemma precondition"
                                                                    env1 pre1
                                                                    (FStar_Pervasives_Native.Some
                                                                    goal_sc) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___19
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    Obj.magic
                                                                    uu___20 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Monad.add_goals
                                                                    sub_goals2))
                                                                    uu___20)))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    uu___15))))
                                                                    uu___13)))
                                                                    uu___10)))))
                                                     uu___6)))) uu___4)))
                              uu___3))) uu___2) in
          FStar_Tactics_Monad.focus uu___1 in
        FStar_Tactics_Monad.wrap_err "apply_lemma" uu___
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar ->
    fun e ->
      let rec aux e1 =
        let uu___ = FStar_TypeChecker_Env.pop_bv e1 in
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv', e') ->
            let uu___1 = FStar_Syntax_Syntax.bv_eq bvar bv' in
            if uu___1
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu___3 = aux e' in
               FStar_Compiler_Util.map_opt uu___3
                 (fun uu___4 ->
                    match uu___4 with
                    | (e'', bv, bvs) -> (e'', bv, (bv' :: bvs)))) in
      let uu___ = aux e in
      FStar_Compiler_Util.map_opt uu___
        (fun uu___1 ->
           match uu___1 with
           | (e', bv, bvs) -> (e', bv, (FStar_Compiler_List.rev bvs)))
let (subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Tactics_Types.goal ->
        (FStar_Syntax_Syntax.bv * FStar_Tactics_Types.goal)
          FStar_Pervasives_Native.option FStar_Tactics_Monad.tac)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun b1 ->
           fun b2 ->
             fun g ->
               let uu___ =
                 let uu___1 = FStar_Tactics_Types.goal_env g in
                 split_env b1 uu___1 in
               match uu___ with
               | FStar_Pervasives_Native.Some (e0, b11, bvs) ->
                   let bs =
                     FStar_Compiler_List.map FStar_Syntax_Syntax.mk_binder
                       (b11 :: bvs) in
                   let t = FStar_Tactics_Types.goal_type g in
                   let uu___1 =
                     let uu___2 = FStar_Syntax_Subst.close_binders bs in
                     let uu___3 = FStar_Syntax_Subst.close bs t in
                     (uu___2, uu___3) in
                   (match uu___1 with
                    | (bs', t') ->
                        let bs'1 =
                          let uu___2 = FStar_Syntax_Syntax.mk_binder b2 in
                          let uu___3 = FStar_Compiler_List.tail bs' in uu___2
                            :: uu___3 in
                        let uu___2 =
                          FStar_TypeChecker_Core.open_binders_in_term e0 bs'1
                            t' in
                        (match uu___2 with
                         | (new_env, bs'', t'') ->
                             let b21 =
                               let uu___3 = FStar_Compiler_List.hd bs'' in
                               uu___3.FStar_Syntax_Syntax.binder_bv in
                             let uu___3 =
                               let uu___4 =
                                 let uu___5 = should_check_goal_uvar g in
                                 FStar_Pervasives_Native.Some uu___5 in
                               let uu___5 =
                                 FStar_Tactics_Monad.goal_typedness_deps g in
                               FStar_Tactics_Monad.new_uvar "subst_goal"
                                 new_env t'' uu___4 uu___5 (rangeof g) in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  FStar_Tactics_Monad.monad_tac () ()
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     (fun uu___4 ->
                                        let uu___4 = Obj.magic uu___4 in
                                        match uu___4 with
                                        | (uvt, uv) ->
                                            let goal' =
                                              FStar_Tactics_Types.mk_goal
                                                new_env uv
                                                g.FStar_Tactics_Types.opts
                                                g.FStar_Tactics_Types.is_guard
                                                g.FStar_Tactics_Types.label in
                                            let sol =
                                              let uu___5 =
                                                FStar_Syntax_Util.abs bs''
                                                  uvt
                                                  FStar_Pervasives_Native.None in
                                              let uu___6 =
                                                FStar_Compiler_List.map
                                                  (fun uu___7 ->
                                                     match uu___7 with
                                                     | {
                                                         FStar_Syntax_Syntax.binder_bv
                                                           = bv;
                                                         FStar_Syntax_Syntax.binder_qual
                                                           = q;
                                                         FStar_Syntax_Syntax.binder_positivity
                                                           = uu___8;
                                                         FStar_Syntax_Syntax.binder_attrs
                                                           = uu___9;_}
                                                         ->
                                                         let uu___10 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             bv in
                                                         FStar_Syntax_Syntax.as_arg
                                                           uu___10) bs in
                                              FStar_Syntax_Util.mk_app uu___5
                                                uu___6 in
                                            let uu___5 = set_solution g sol in
                                            Obj.magic
                                              (FStar_Class_Monad.op_let_Bang
                                                 FStar_Tactics_Monad.monad_tac
                                                 () () uu___5
                                                 (fun uu___6 ->
                                                    (fun uu___6 ->
                                                       let uu___6 =
                                                         Obj.magic uu___6 in
                                                       Obj.magic
                                                         (FStar_Class_Monad.return
                                                            FStar_Tactics_Monad.monad_tac
                                                            ()
                                                            (Obj.magic
                                                               (FStar_Pervasives_Native.Some
                                                                  (b21,
                                                                    goal')))))
                                                      uu___6))) uu___4))))
               | FStar_Pervasives_Native.None ->
                   Obj.magic
                     (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                        () (Obj.magic FStar_Pervasives_Native.None))) uu___2
          uu___1 uu___
let (rewrite :
  FStar_Reflection_V2_Data.binding -> unit FStar_Tactics_Monad.tac) =
  fun hh ->
    let uu___ =
      FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
        (Obj.magic FStar_Tactics_Monad.cur_goal)
        (fun uu___1 ->
           (fun goal ->
              let goal = Obj.magic goal in
              let h = binding_to_binder hh in
              let bv = h.FStar_Syntax_Syntax.binder_bv in
              let uu___1 =
                FStar_Tactics_Monad.if_verbose
                  (fun uu___2 ->
                     let uu___3 =
                       FStar_Class_Show.show FStar_Syntax_Print.showable_bv
                         bv in
                     let uu___4 =
                       FStar_Class_Show.show FStar_Syntax_Print.showable_term
                         bv.FStar_Syntax_Syntax.sort in
                     FStar_Compiler_Util.print2 "+++Rewrite %s : %s\n" uu___3
                       uu___4) in
              Obj.magic
                (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac
                   () () uu___1
                   (fun uu___2 ->
                      (fun uu___2 ->
                         let uu___2 = Obj.magic uu___2 in
                         let uu___3 =
                           let uu___4 = FStar_Tactics_Types.goal_env goal in
                           split_env bv uu___4 in
                         match uu___3 with
                         | FStar_Pervasives_Native.None ->
                             Obj.magic
                               (FStar_Tactics_Monad.fail
                                  "binder not found in environment")
                         | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                             let uu___4 =
                               destruct_eq e0 bv1.FStar_Syntax_Syntax.sort in
                             (match uu___4 with
                              | FStar_Pervasives_Native.Some (x, e) ->
                                  let uu___5 =
                                    let uu___6 =
                                      FStar_Syntax_Subst.compress x in
                                    uu___6.FStar_Syntax_Syntax.n in
                                  (match uu___5 with
                                   | FStar_Syntax_Syntax.Tm_name x1 ->
                                       let s =
                                         [FStar_Syntax_Syntax.NT (x1, e)] in
                                       let t =
                                         FStar_Tactics_Types.goal_type goal in
                                       let bs =
                                         FStar_Compiler_List.map
                                           FStar_Syntax_Syntax.mk_binder bvs in
                                       let uu___6 =
                                         let uu___7 =
                                           FStar_Syntax_Subst.close_binders
                                             bs in
                                         let uu___8 =
                                           FStar_Syntax_Subst.close bs t in
                                         (uu___7, uu___8) in
                                       (match uu___6 with
                                        | (bs', t') ->
                                            let uu___7 =
                                              let uu___8 =
                                                FStar_Syntax_Subst.subst_binders
                                                  s bs' in
                                              let uu___9 =
                                                FStar_Syntax_Subst.subst s t' in
                                              (uu___8, uu___9) in
                                            (match uu___7 with
                                             | (bs'1, t'1) ->
                                                 let e01 =
                                                   FStar_TypeChecker_Env.push_bvs
                                                     e0 [bv1] in
                                                 let uu___8 =
                                                   FStar_TypeChecker_Core.open_binders_in_term
                                                     e01 bs'1 t'1 in
                                                 (match uu___8 with
                                                  | (new_env, bs'', t'') ->
                                                      let uu___9 =
                                                        let uu___10 =
                                                          let uu___11 =
                                                            should_check_goal_uvar
                                                              goal in
                                                          FStar_Pervasives_Native.Some
                                                            uu___11 in
                                                        let uu___11 =
                                                          FStar_Tactics_Monad.goal_typedness_deps
                                                            goal in
                                                        FStar_Tactics_Monad.new_uvar
                                                          "rewrite" new_env
                                                          t'' uu___10 uu___11
                                                          (rangeof goal) in
                                                      Obj.magic
                                                        (FStar_Class_Monad.op_let_Bang
                                                           FStar_Tactics_Monad.monad_tac
                                                           () ()
                                                           (Obj.magic uu___9)
                                                           (fun uu___10 ->
                                                              (fun uu___10 ->
                                                                 let uu___10
                                                                   =
                                                                   Obj.magic
                                                                    uu___10 in
                                                                 match uu___10
                                                                 with
                                                                 | (uvt, uv)
                                                                    ->
                                                                    let goal'
                                                                    =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    new_env
                                                                    uv
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.is_guard
                                                                    goal.FStar_Tactics_Types.label in
                                                                    let sol =
                                                                    let uu___11
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    bs'' uvt
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu___12
                                                                    =
                                                                    FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv2;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___14;
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    = uu___15;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___16;_}
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv2 in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu___17)
                                                                    bs in
                                                                    FStar_Syntax_Util.mk_app
                                                                    uu___11
                                                                    uu___12 in
                                                                    let uu___11
                                                                    =
                                                                    set_solution
                                                                    goal sol in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___11
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    uu___12 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Monad.replace_cur
                                                                    goal'))
                                                                    uu___12)))
                                                                uu___10)))))
                                   | uu___6 ->
                                       Obj.magic
                                         (FStar_Tactics_Monad.fail
                                            "Not an equality hypothesis with a variable on the LHS"))
                              | uu___5 ->
                                  Obj.magic
                                    (FStar_Tactics_Monad.fail
                                       "Not an equality hypothesis"))) uu___2)))
             uu___1) in
    FStar_Tactics_Monad.wrap_err "rewrite" uu___
let (rename_to :
  FStar_Reflection_V2_Data.binding ->
    Prims.string -> FStar_Reflection_V2_Data.binding FStar_Tactics_Monad.tac)
  =
  fun b ->
    fun s ->
      let uu___ =
        Obj.magic
          (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
             (Obj.magic FStar_Tactics_Monad.cur_goal)
             (fun uu___1 ->
                (fun goal ->
                   let goal = Obj.magic goal in
                   let bv = binding_to_bv b in
                   let bv' =
                     let uu___1 =
                       let uu___2 =
                         let uu___3 =
                           let uu___4 =
                             FStar_Ident.range_of_id
                               bv.FStar_Syntax_Syntax.ppname in
                           (s, uu___4) in
                         FStar_Ident.mk_ident uu___3 in
                       {
                         FStar_Syntax_Syntax.ppname = uu___2;
                         FStar_Syntax_Syntax.index =
                           (bv.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort =
                           (bv.FStar_Syntax_Syntax.sort)
                       } in
                     FStar_Syntax_Syntax.freshen_bv uu___1 in
                   let uu___1 = subst_goal bv bv' goal in
                   Obj.magic
                     (FStar_Class_Monad.op_let_Bang
                        FStar_Tactics_Monad.monad_tac () ()
                        (Obj.magic uu___1)
                        (fun uu___2 ->
                           (fun uu___2 ->
                              let uu___2 = Obj.magic uu___2 in
                              match uu___2 with
                              | FStar_Pervasives_Native.None ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Monad.fail
                                          "binder not found in environment"))
                              | FStar_Pervasives_Native.Some (bv'1, goal1) ->
                                  Obj.magic
                                    (Obj.repr
                                       (let uu___3 =
                                          FStar_Tactics_Monad.replace_cur
                                            goal1 in
                                        FStar_Class_Monad.op_let_Bang
                                          FStar_Tactics_Monad.monad_tac () ()
                                          uu___3
                                          (fun uu___4 ->
                                             (fun uu___4 ->
                                                let uu___4 = Obj.magic uu___4 in
                                                let uniq =
                                                  FStar_BigInt.of_int_fs
                                                    bv'1.FStar_Syntax_Syntax.index in
                                                Obj.magic
                                                  (FStar_Class_Monad.return
                                                     FStar_Tactics_Monad.monad_tac
                                                     ()
                                                     (Obj.magic
                                                        {
                                                          FStar_Reflection_V2_Data.uniq1
                                                            = uniq;
                                                          FStar_Reflection_V2_Data.sort3
                                                            =
                                                            (b.FStar_Reflection_V2_Data.sort3);
                                                          FStar_Reflection_V2_Data.ppname3
                                                            =
                                                            (FStar_Compiler_Sealed.seal
                                                               s)
                                                        }))) uu___4))))
                             uu___2))) uu___1)) in
      FStar_Tactics_Monad.wrap_err "rename_to" uu___
let (var_retype :
  FStar_Reflection_V2_Data.binding -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let uu___ =
      FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
        (Obj.magic FStar_Tactics_Monad.cur_goal)
        (fun uu___1 ->
           (fun goal ->
              let goal = Obj.magic goal in
              let bv = binding_to_bv b in
              let uu___1 =
                let uu___2 = FStar_Tactics_Types.goal_env goal in
                split_env bv uu___2 in
              match uu___1 with
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (FStar_Tactics_Monad.fail
                       "binder is not present in environment")
              | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                  let uu___2 = FStar_Syntax_Util.type_u () in
                  (match uu___2 with
                   | (ty, u) ->
                       let goal_sc = should_check_goal_uvar goal in
                       let uu___3 =
                         let uu___4 =
                           FStar_Tactics_Monad.goal_typedness_deps goal in
                         FStar_Tactics_Monad.new_uvar "binder_retype" e0 ty
                           (FStar_Pervasives_Native.Some goal_sc) uu___4
                           (rangeof goal) in
                       Obj.magic
                         (FStar_Class_Monad.op_let_Bang
                            FStar_Tactics_Monad.monad_tac () ()
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun uu___4 ->
                                  let uu___4 = Obj.magic uu___4 in
                                  match uu___4 with
                                  | (t', u_t') ->
                                      let bv'' =
                                        {
                                          FStar_Syntax_Syntax.ppname =
                                            (bv1.FStar_Syntax_Syntax.ppname);
                                          FStar_Syntax_Syntax.index =
                                            (bv1.FStar_Syntax_Syntax.index);
                                          FStar_Syntax_Syntax.sort = t'
                                        } in
                                      let s =
                                        let uu___5 =
                                          let uu___6 =
                                            let uu___7 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                bv'' in
                                            (bv1, uu___7) in
                                          FStar_Syntax_Syntax.NT uu___6 in
                                        [uu___5] in
                                      let bvs1 =
                                        FStar_Compiler_List.map
                                          (fun b1 ->
                                             let uu___5 =
                                               FStar_Syntax_Subst.subst s
                                                 b1.FStar_Syntax_Syntax.sort in
                                             {
                                               FStar_Syntax_Syntax.ppname =
                                                 (b1.FStar_Syntax_Syntax.ppname);
                                               FStar_Syntax_Syntax.index =
                                                 (b1.FStar_Syntax_Syntax.index);
                                               FStar_Syntax_Syntax.sort =
                                                 uu___5
                                             }) bvs in
                                      let env' =
                                        FStar_TypeChecker_Env.push_bvs e0
                                          (bv'' :: bvs1) in
                                      Obj.magic
                                        (FStar_Class_Monad.op_let_Bang
                                           FStar_Tactics_Monad.monad_tac ()
                                           () FStar_Tactics_Monad.dismiss
                                           (fun uu___5 ->
                                              (fun uu___5 ->
                                                 let uu___5 =
                                                   Obj.magic uu___5 in
                                                 let new_goal =
                                                   let uu___6 =
                                                     FStar_Tactics_Types.goal_with_env
                                                       goal env' in
                                                   let uu___7 =
                                                     let uu___8 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal in
                                                     FStar_Syntax_Subst.subst
                                                       s uu___8 in
                                                   FStar_Tactics_Monad.goal_with_type
                                                     uu___6 uu___7 in
                                                 let uu___6 =
                                                   FStar_Tactics_Monad.add_goals
                                                     [new_goal] in
                                                 Obj.magic
                                                   (FStar_Class_Monad.op_let_Bang
                                                      FStar_Tactics_Monad.monad_tac
                                                      () () uu___6
                                                      (fun uu___7 ->
                                                         (fun uu___7 ->
                                                            let uu___7 =
                                                              Obj.magic
                                                                uu___7 in
                                                            let uu___8 =
                                                              FStar_Syntax_Util.mk_eq2
                                                                (FStar_Syntax_Syntax.U_succ
                                                                   u) ty
                                                                bv1.FStar_Syntax_Syntax.sort
                                                                t' in
                                                            Obj.magic
                                                              (FStar_Tactics_Monad.add_irrelevant_goal
                                                                 goal
                                                                 "binder_retype equation"
                                                                 e0 uu___8
                                                                 (FStar_Pervasives_Native.Some
                                                                    goal_sc)))
                                                           uu___7))) uu___5)))
                                 uu___4)))) uu___1) in
    FStar_Tactics_Monad.wrap_err "binder_retype" uu___
let (norm_binding_type :
  FStar_Pervasives.norm_step Prims.list ->
    FStar_Reflection_V2_Data.binding -> unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    fun b ->
      let uu___ =
        FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
          (Obj.magic FStar_Tactics_Monad.cur_goal)
          (fun uu___1 ->
             (fun goal ->
                let goal = Obj.magic goal in
                let bv = binding_to_bv b in
                let uu___1 =
                  let uu___2 = FStar_Tactics_Types.goal_env goal in
                  split_env bv uu___2 in
                match uu___1 with
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (FStar_Tactics_Monad.fail
                         "binder is not present in environment")
                | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                    let steps =
                      let uu___2 =
                        FStar_TypeChecker_Cfg.translate_norm_steps s in
                      FStar_Compiler_List.op_At
                        [FStar_TypeChecker_Env.Reify;
                        FStar_TypeChecker_Env.UnfoldTac] uu___2 in
                    let sort' =
                      normalize steps e0 bv1.FStar_Syntax_Syntax.sort in
                    let bv' =
                      {
                        FStar_Syntax_Syntax.ppname =
                          (bv1.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (bv1.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = FStar_TypeChecker_Env.push_bvs e0 (bv' :: bvs) in
                    let uu___2 = FStar_Tactics_Types.goal_with_env goal env' in
                    Obj.magic (FStar_Tactics_Monad.replace_cur uu___2))
               uu___1) in
      FStar_Tactics_Monad.wrap_err "norm_binding_type" uu___
let (revert : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
      (Obj.magic FStar_Tactics_Monad.cur_goal)
      (fun uu___1 ->
         (fun goal ->
            let goal = Obj.magic goal in
            let uu___1 =
              let uu___2 = FStar_Tactics_Types.goal_env goal in
              FStar_TypeChecker_Env.pop_bv uu___2 in
            match uu___1 with
            | FStar_Pervasives_Native.None ->
                Obj.magic
                  (FStar_Tactics_Monad.fail "Cannot revert; empty context")
            | FStar_Pervasives_Native.Some (x, env') ->
                let typ' =
                  let uu___2 =
                    let uu___3 = FStar_Syntax_Syntax.mk_binder x in [uu___3] in
                  let uu___3 =
                    let uu___4 = FStar_Tactics_Types.goal_type goal in
                    FStar_Syntax_Syntax.mk_Total uu___4 in
                  FStar_Syntax_Util.arrow uu___2 uu___3 in
                let uu___2 =
                  let uu___3 =
                    let uu___4 = should_check_goal_uvar goal in
                    FStar_Pervasives_Native.Some uu___4 in
                  let uu___4 = FStar_Tactics_Monad.goal_typedness_deps goal in
                  FStar_Tactics_Monad.new_uvar "revert" env' typ' uu___3
                    uu___4 (rangeof goal) in
                Obj.magic
                  (FStar_Class_Monad.op_let_Bang
                     FStar_Tactics_Monad.monad_tac () () (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___3 = Obj.magic uu___3 in
                           match uu___3 with
                           | (r, u_r) ->
                               let uu___4 =
                                 let uu___5 =
                                   let uu___6 =
                                     let uu___7 =
                                       let uu___8 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_Syntax_Syntax.as_arg uu___8 in
                                     [uu___7] in
                                   let uu___7 =
                                     let uu___8 =
                                       FStar_Tactics_Types.goal_type goal in
                                     uu___8.FStar_Syntax_Syntax.pos in
                                   FStar_Syntax_Syntax.mk_Tm_app r uu___6
                                     uu___7 in
                                 set_solution goal uu___5 in
                               Obj.magic
                                 (FStar_Class_Monad.op_let_Bang
                                    FStar_Tactics_Monad.monad_tac () ()
                                    uu___4
                                    (fun uu___5 ->
                                       (fun uu___5 ->
                                          let uu___5 = Obj.magic uu___5 in
                                          let g =
                                            FStar_Tactics_Types.mk_goal env'
                                              u_r
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.is_guard
                                              goal.FStar_Tactics_Types.label in
                                          Obj.magic
                                            (FStar_Tactics_Monad.replace_cur
                                               g)) uu___5))) uu___3))) uu___1)
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv ->
    fun t ->
      let uu___ = FStar_Syntax_Free.names t in
      FStar_Compiler_Set.mem FStar_Syntax_Syntax.ord_bv bv uu___
let (clear :
  FStar_Reflection_V2_Data.binding -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let bv = binding_to_bv b in
    FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
      (Obj.magic FStar_Tactics_Monad.cur_goal)
      (fun uu___ ->
         (fun goal ->
            let goal = Obj.magic goal in
            let uu___ =
              FStar_Tactics_Monad.if_verbose
                (fun uu___1 ->
                   let uu___2 = binding_to_string b in
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = FStar_Tactics_Types.goal_env goal in
                         FStar_TypeChecker_Env.all_binders uu___6 in
                       FStar_Compiler_List.length uu___5 in
                     FStar_Class_Show.show
                       (FStar_Class_Show.printableshow
                          FStar_Class_Printable.printable_nat) uu___4 in
                   FStar_Compiler_Util.print2
                     "Clear of (%s), env has %s binders\n" uu___2 uu___3) in
            Obj.magic
              (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                 () uu___
                 (fun uu___1 ->
                    (fun uu___1 ->
                       let uu___1 = Obj.magic uu___1 in
                       let uu___2 =
                         let uu___3 = FStar_Tactics_Types.goal_env goal in
                         split_env bv uu___3 in
                       match uu___2 with
                       | FStar_Pervasives_Native.None ->
                           Obj.magic
                             (FStar_Tactics_Monad.fail
                                "Cannot clear; binder not in environment")
                       | FStar_Pervasives_Native.Some (e', bv1, bvs) ->
                           let rec check bvs1 =
                             match bvs1 with
                             | [] ->
                                 FStar_Class_Monad.return
                                   FStar_Tactics_Monad.monad_tac ()
                                   (Obj.repr ())
                             | bv'::bvs2 ->
                                 let uu___3 =
                                   free_in bv1 bv'.FStar_Syntax_Syntax.sort in
                                 if uu___3
                                 then
                                   let uu___4 =
                                     let uu___5 =
                                       FStar_Class_Show.show
                                         FStar_Syntax_Print.showable_bv bv' in
                                     FStar_Compiler_Util.format1
                                       "Cannot clear; binder present in the type of %s"
                                       uu___5 in
                                   FStar_Tactics_Monad.fail uu___4
                                 else check bvs2 in
                           let uu___3 =
                             let uu___4 = FStar_Tactics_Types.goal_type goal in
                             free_in bv1 uu___4 in
                           if uu___3
                           then
                             Obj.magic
                               (FStar_Tactics_Monad.fail
                                  "Cannot clear; binder present in goal")
                           else
                             (let uu___5 = check bvs in
                              Obj.magic
                                (FStar_Class_Monad.op_let_Bang
                                   FStar_Tactics_Monad.monad_tac () () uu___5
                                   (fun uu___6 ->
                                      (fun uu___6 ->
                                         let uu___6 = Obj.magic uu___6 in
                                         let env' =
                                           FStar_TypeChecker_Env.push_bvs e'
                                             bvs in
                                         let uu___7 =
                                           let uu___8 =
                                             FStar_Tactics_Types.goal_type
                                               goal in
                                           let uu___9 =
                                             let uu___10 =
                                               should_check_goal_uvar goal in
                                             FStar_Pervasives_Native.Some
                                               uu___10 in
                                           let uu___10 =
                                             FStar_Tactics_Monad.goal_typedness_deps
                                               goal in
                                           FStar_Tactics_Monad.new_uvar
                                             "clear.witness" env' uu___8
                                             uu___9 uu___10 (rangeof goal) in
                                         Obj.magic
                                           (FStar_Class_Monad.op_let_Bang
                                              FStar_Tactics_Monad.monad_tac
                                              () () (Obj.magic uu___7)
                                              (fun uu___8 ->
                                                 (fun uu___8 ->
                                                    let uu___8 =
                                                      Obj.magic uu___8 in
                                                    match uu___8 with
                                                    | (ut, uvar_ut) ->
                                                        let uu___9 =
                                                          set_solution goal
                                                            ut in
                                                        Obj.magic
                                                          (FStar_Class_Monad.op_let_Bang
                                                             FStar_Tactics_Monad.monad_tac
                                                             () () uu___9
                                                             (fun uu___10 ->
                                                                (fun uu___10
                                                                   ->
                                                                   let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    uu___10 in
                                                                   let uu___11
                                                                    =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env'
                                                                    uvar_ut
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.is_guard
                                                                    goal.FStar_Tactics_Types.label in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Monad.replace_cur
                                                                    uu___11))
                                                                  uu___10)))
                                                   uu___8))) uu___6))))
                      uu___1))) uu___)
let (clear_top : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
      (Obj.magic FStar_Tactics_Monad.cur_goal)
      (fun uu___1 ->
         (fun goal ->
            let goal = Obj.magic goal in
            let uu___1 =
              let uu___2 = FStar_Tactics_Types.goal_env goal in
              FStar_TypeChecker_Env.pop_bv uu___2 in
            match uu___1 with
            | FStar_Pervasives_Native.None ->
                Obj.magic
                  (FStar_Tactics_Monad.fail "Cannot clear; empty context")
            | FStar_Pervasives_Native.Some (x, uu___2) ->
                let uu___3 = bv_to_binding x in Obj.magic (clear uu___3))
           uu___1)
let (prune : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
      (Obj.magic FStar_Tactics_Monad.cur_goal)
      (fun uu___ ->
         (fun g ->
            let g = Obj.magic g in
            let ctx = FStar_Tactics_Types.goal_env g in
            let ctx' =
              let uu___ = FStar_Ident.path_of_text s in
              FStar_TypeChecker_Env.rem_proof_ns ctx uu___ in
            let g' = FStar_Tactics_Types.goal_with_env g ctx' in
            Obj.magic (FStar_Tactics_Monad.replace_cur g')) uu___)
let (addns : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
      (Obj.magic FStar_Tactics_Monad.cur_goal)
      (fun uu___ ->
         (fun g ->
            let g = Obj.magic g in
            let ctx = FStar_Tactics_Types.goal_env g in
            let ctx' =
              let uu___ = FStar_Ident.path_of_text s in
              FStar_TypeChecker_Env.add_proof_ns ctx uu___ in
            let g' = FStar_Tactics_Types.goal_with_env g ctx' in
            Obj.magic (FStar_Tactics_Monad.replace_cur g')) uu___)
let (guard_formula :
  FStar_TypeChecker_Common.guard_t -> FStar_Syntax_Syntax.term) =
  fun g ->
    match g.FStar_TypeChecker_Common.guard_f with
    | FStar_TypeChecker_Common.Trivial -> FStar_Syntax_Util.t_true
    | FStar_TypeChecker_Common.NonTrivial f -> f
let (_t_trefl :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun allow_guards ->
    fun l ->
      fun r ->
        let should_register_trefl g =
          let should_register = true in
          let skip_register = false in
          let uu___ =
            let uu___1 = FStar_Options.compat_pre_core_should_register () in
            Prims.op_Negation uu___1 in
          if uu___
          then skip_register
          else
            (let is_uvar_untyped_or_already_checked u =
               let dec =
                 FStar_Syntax_Unionfind.find_decoration
                   u.FStar_Syntax_Syntax.ctx_uvar_head in
               match dec.FStar_Syntax_Syntax.uvar_decoration_should_check
               with
               | FStar_Syntax_Syntax.Allow_untyped uu___2 -> true
               | FStar_Syntax_Syntax.Already_checked -> true
               | uu___2 -> false in
             let is_uvar t =
               let head = FStar_Syntax_Util.leftmost_head t in
               let uu___2 =
                 let uu___3 = FStar_Syntax_Subst.compress head in
                 uu___3.FStar_Syntax_Syntax.n in
               match uu___2 with
               | FStar_Syntax_Syntax.Tm_uvar (u, uu___3) ->
                   FStar_Pervasives.Inl (u, head, t)
               | uu___3 -> FStar_Pervasives.Inr t in
             let is_allow_untyped_uvar t =
               let uu___2 = is_uvar t in
               match uu___2 with
               | FStar_Pervasives.Inr uu___3 -> false
               | FStar_Pervasives.Inl (u, uu___3, uu___4) ->
                   is_uvar_untyped_or_already_checked u in
             let t =
               FStar_Syntax_Util.ctx_uvar_typ
                 g.FStar_Tactics_Types.goal_ctx_uvar in
             let uvars = FStar_Syntax_Free.uvars t in
             let uu___2 =
               FStar_Compiler_Set.for_all FStar_Syntax_Free.ord_ctx_uvar
                 is_uvar_untyped_or_already_checked uvars in
             if uu___2
             then skip_register
             else
               (let uu___4 =
                  let t1 =
                    let uu___5 = FStar_Syntax_Util.un_squash t in
                    match uu___5 with
                    | FStar_Pervasives_Native.None -> t
                    | FStar_Pervasives_Native.Some t2 -> t2 in
                  FStar_Syntax_Util.leftmost_head_and_args t1 in
                match uu___4 with
                | (head, args) ->
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 = FStar_Syntax_Util.un_uinst head in
                          FStar_Syntax_Subst.compress uu___8 in
                        uu___7.FStar_Syntax_Syntax.n in
                      (uu___6, args) in
                    (match uu___5 with
                     | (FStar_Syntax_Syntax.Tm_fvar fv,
                        (ty, uu___6)::(t1, uu___7)::(t2, uu___8)::[]) when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu___9 =
                           (is_allow_untyped_uvar t1) ||
                             (is_allow_untyped_uvar t2) in
                         if uu___9
                         then skip_register
                         else
                           (let uu___11 =
                              FStar_Tactics_Monad.is_goal_safe_as_well_typed
                                g in
                            if uu___11
                            then
                              let check_uvar_subtype u t3 =
                                let env1 =
                                  let uu___12 =
                                    FStar_Tactics_Types.goal_env g in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___12.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___12.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___12.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      ((g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___12.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___12.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___12.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___12.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___12.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.attrtab =
                                      (uu___12.FStar_TypeChecker_Env.attrtab);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___12.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___12.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___12.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___12.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___12.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___12.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq_strict =
                                      (uu___12.FStar_TypeChecker_Env.use_eq_strict);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___12.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___12.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___12.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___12.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.phase1 =
                                      (uu___12.FStar_TypeChecker_Env.phase1);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___12.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___12.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.uvar_subtyping =
                                      (uu___12.FStar_TypeChecker_Env.uvar_subtyping);
                                    FStar_TypeChecker_Env.intactics =
                                      (uu___12.FStar_TypeChecker_Env.intactics);
                                    FStar_TypeChecker_Env.nocoerce =
                                      (uu___12.FStar_TypeChecker_Env.nocoerce);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___12.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                      =
                                      (uu___12.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___12.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                      =
                                      (uu___12.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                    FStar_TypeChecker_Env.teq_nosmt_force =
                                      (uu___12.FStar_TypeChecker_Env.teq_nosmt_force);
                                    FStar_TypeChecker_Env.subtype_nosmt_force
                                      =
                                      (uu___12.FStar_TypeChecker_Env.subtype_nosmt_force);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___12.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___12.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.fv_delta_depths =
                                      (uu___12.FStar_TypeChecker_Env.fv_delta_depths);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___12.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___12.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                      =
                                      (uu___12.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___12.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.mpreprocess =
                                      (uu___12.FStar_TypeChecker_Env.mpreprocess);
                                    FStar_TypeChecker_Env.postprocess =
                                      (uu___12.FStar_TypeChecker_Env.postprocess);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___12.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___12.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___12.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.nbe =
                                      (uu___12.FStar_TypeChecker_Env.nbe);
                                    FStar_TypeChecker_Env.strict_args_tab =
                                      (uu___12.FStar_TypeChecker_Env.strict_args_tab);
                                    FStar_TypeChecker_Env.erasable_types_tab
                                      =
                                      (uu___12.FStar_TypeChecker_Env.erasable_types_tab);
                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                      =
                                      (uu___12.FStar_TypeChecker_Env.enable_defer_to_tac);
                                    FStar_TypeChecker_Env.unif_allow_ref_guards
                                      =
                                      (uu___12.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                    FStar_TypeChecker_Env.erase_erasable_args
                                      =
                                      (uu___12.FStar_TypeChecker_Env.erase_erasable_args);
                                    FStar_TypeChecker_Env.core_check =
                                      (uu___12.FStar_TypeChecker_Env.core_check)
                                  } in
                                let uu___12 =
                                  FStar_TypeChecker_Core.compute_term_type_handle_guards
                                    env1 t3
                                    (fun uu___13 -> fun uu___14 -> true) in
                                match uu___12 with
                                | FStar_Pervasives.Inr uu___13 -> false
                                | FStar_Pervasives.Inl (uu___13, t_ty) ->
                                    let uu___14 =
                                      FStar_TypeChecker_Core.check_term_subtyping
                                        env1 ty t_ty in
                                    (match uu___14 with
                                     | FStar_Pervasives.Inl
                                         (FStar_Pervasives_Native.None) ->
                                         (FStar_Tactics_Monad.mark_uvar_as_already_checked
                                            u;
                                          true)
                                     | uu___15 -> false) in
                              let uu___12 =
                                let uu___13 = is_uvar t1 in
                                let uu___14 = is_uvar t2 in
                                (uu___13, uu___14) in
                              match uu___12 with
                              | (FStar_Pervasives.Inl (u, uu___13, tu),
                                 FStar_Pervasives.Inr uu___14) ->
                                  let uu___15 = check_uvar_subtype u tu in
                                  (if uu___15
                                   then skip_register
                                   else should_register)
                              | (FStar_Pervasives.Inr uu___13,
                                 FStar_Pervasives.Inl (u, uu___14, tu)) ->
                                  let uu___15 = check_uvar_subtype u tu in
                                  (if uu___15
                                   then skip_register
                                   else should_register)
                              | uu___13 -> should_register
                            else should_register)
                     | uu___6 -> should_register))) in
        FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
          (Obj.magic FStar_Tactics_Monad.cur_goal)
          (fun uu___ ->
             (fun g ->
                let g = Obj.magic g in
                let should_check = should_check_goal_uvar g in
                (let uu___1 = should_register_trefl g in
                 if uu___1 then FStar_Tactics_Monad.register_goal g else ());
                (let must_tot = true in
                 let attempt uu___2 uu___1 =
                   (fun l1 ->
                      fun r1 ->
                        let uu___1 =
                          let uu___2 = FStar_Tactics_Types.goal_env g in
                          do_unify_maybe_guards allow_guards must_tot uu___2
                            l1 r1 in
                        Obj.magic
                          (FStar_Class_Monad.op_let_Bang
                             FStar_Tactics_Monad.monad_tac () ()
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                (fun uu___2 ->
                                   let uu___2 = Obj.magic uu___2 in
                                   match uu___2 with
                                   | FStar_Pervasives_Native.None ->
                                       Obj.magic
                                         (FStar_Class_Monad.return
                                            FStar_Tactics_Monad.monad_tac ()
                                            (Obj.magic false))
                                   | FStar_Pervasives_Native.Some guard ->
                                       let uu___3 =
                                         solve' g FStar_Syntax_Util.exp_unit in
                                       Obj.magic
                                         (FStar_Class_Monad.op_let_Bang
                                            FStar_Tactics_Monad.monad_tac ()
                                            () uu___3
                                            (fun uu___4 ->
                                               (fun uu___4 ->
                                                  let uu___4 =
                                                    Obj.magic uu___4 in
                                                  if allow_guards
                                                  then
                                                    Obj.magic
                                                      (Obj.repr
                                                         (let uu___5 =
                                                            let uu___6 =
                                                              FStar_Tactics_Types.goal_env
                                                                g in
                                                            let uu___7 =
                                                              guard_formula
                                                                guard in
                                                            FStar_Tactics_Monad.goal_of_guard
                                                              "t_trefl"
                                                              uu___6 uu___7
                                                              (FStar_Pervasives_Native.Some
                                                                 should_check)
                                                              (rangeof g) in
                                                          FStar_Class_Monad.op_let_Bang
                                                            FStar_Tactics_Monad.monad_tac
                                                            () ()
                                                            (Obj.magic uu___5)
                                                            (fun uu___6 ->
                                                               (fun goal ->
                                                                  let goal =
                                                                    Obj.magic
                                                                    goal in
                                                                  let uu___6
                                                                    =
                                                                    FStar_Tactics_Monad.push_goals
                                                                    [goal] in
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___6
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    uu___7 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    true)))
                                                                    uu___7)))
                                                                 uu___6)))
                                                  else
                                                    Obj.magic
                                                      (Obj.repr
                                                         (let uu___6 =
                                                            FStar_TypeChecker_Env.is_trivial_guard_formula
                                                              guard in
                                                          if uu___6
                                                          then
                                                            Obj.repr
                                                              (FStar_Class_Monad.return
                                                                 FStar_Tactics_Monad.monad_tac
                                                                 ()
                                                                 (Obj.magic
                                                                    true))
                                                          else
                                                            Obj.repr
                                                              (FStar_Compiler_Effect.failwith
                                                                 "internal error: _t_refl: guard is not trivial"))))
                                                 uu___4))) uu___2))) uu___2
                     uu___1 in
                 let uu___1 = attempt l r in
                 Obj.magic
                   (FStar_Class_Monad.op_let_Bang
                      FStar_Tactics_Monad.monad_tac () () (Obj.magic uu___1)
                      (fun uu___2 ->
                         (fun uu___2 ->
                            let uu___2 = Obj.magic uu___2 in
                            if uu___2
                            then
                              Obj.magic
                                (FStar_Class_Monad.return
                                   FStar_Tactics_Monad.monad_tac ()
                                   (Obj.repr ()))
                            else
                              (let norm1 =
                                 let uu___3 = FStar_Tactics_Types.goal_env g in
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Env.UnfoldUntil
                                      FStar_Syntax_Syntax.delta_constant;
                                   FStar_TypeChecker_Env.Primops;
                                   FStar_TypeChecker_Env.UnfoldTac] uu___3 in
                               let uu___3 =
                                 let uu___4 = norm1 l in
                                 let uu___5 = norm1 r in
                                 attempt uu___4 uu___5 in
                               Obj.magic
                                 (FStar_Class_Monad.op_let_Bang
                                    FStar_Tactics_Monad.monad_tac () ()
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun uu___4 ->
                                          let uu___4 = Obj.magic uu___4 in
                                          if uu___4
                                          then
                                            Obj.magic
                                              (FStar_Class_Monad.return
                                                 FStar_Tactics_Monad.monad_tac
                                                 () (Obj.repr ()))
                                          else
                                            (let uu___5 =
                                               let uu___6 =
                                                 let uu___7 =
                                                   FStar_Tactics_Types.goal_env
                                                     g in
                                                 tts uu___7 in
                                               FStar_TypeChecker_Err.print_discrepancy
                                                 uu___6 l r in
                                             match uu___5 with
                                             | (ls, rs) ->
                                                 Obj.magic
                                                   (fail2
                                                      "cannot unify (%s) and (%s)"
                                                      ls rs))) uu___4))))
                           uu___2)))) uu___)
let (t_trefl : Prims.bool -> unit FStar_Tactics_Monad.tac) =
  fun allow_guards ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            (Obj.magic FStar_Tactics_Monad.cur_goal)
            (fun uu___3 ->
               (fun g ->
                  let g = Obj.magic g in
                  let uu___3 =
                    let uu___4 = FStar_Tactics_Types.goal_env g in
                    let uu___5 = FStar_Tactics_Types.goal_type g in
                    destruct_eq uu___4 uu___5 in
                  match uu___3 with
                  | FStar_Pervasives_Native.Some (l, r) ->
                      Obj.magic (_t_trefl allow_guards l r)
                  | FStar_Pervasives_Native.None ->
                      let uu___4 =
                        let uu___5 = FStar_Tactics_Types.goal_env g in
                        let uu___6 = FStar_Tactics_Types.goal_type g in
                        tts uu___5 uu___6 in
                      Obj.magic (fail1 "not an equality (%s)" uu___4)) uu___3) in
        FStar_Tactics_Monad.catch uu___2 in
      FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
        (Obj.magic uu___1)
        (fun uu___2 ->
           (fun uu___2 ->
              let uu___2 = Obj.magic uu___2 in
              match uu___2 with
              | FStar_Pervasives.Inr v ->
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.repr ()))
              | FStar_Pervasives.Inl exn ->
                  Obj.magic (FStar_Tactics_Monad.traise exn)) uu___2) in
    FStar_Tactics_Monad.wrap_err "t_trefl" uu___
let (dup : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
      (Obj.magic FStar_Tactics_Monad.cur_goal)
      (fun uu___1 ->
         (fun g ->
            let g = Obj.magic g in
            let goal_sc = should_check_goal_uvar g in
            let env1 = FStar_Tactics_Types.goal_env g in
            let uu___1 =
              let uu___2 = FStar_Tactics_Types.goal_type g in
              let uu___3 =
                let uu___4 = should_check_goal_uvar g in
                FStar_Pervasives_Native.Some uu___4 in
              let uu___4 = FStar_Tactics_Monad.goal_typedness_deps g in
              FStar_Tactics_Monad.new_uvar "dup" env1 uu___2 uu___3 uu___4
                (rangeof g) in
            Obj.magic
              (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                 () (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun uu___2 ->
                       let uu___2 = Obj.magic uu___2 in
                       match uu___2 with
                       | (u, u_uvar) ->
                           (FStar_Tactics_Monad.mark_uvar_as_already_checked
                              g.FStar_Tactics_Types.goal_ctx_uvar;
                            (let g' =
                               {
                                 FStar_Tactics_Types.goal_main_env =
                                   (g.FStar_Tactics_Types.goal_main_env);
                                 FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                                 FStar_Tactics_Types.opts =
                                   (g.FStar_Tactics_Types.opts);
                                 FStar_Tactics_Types.is_guard =
                                   (g.FStar_Tactics_Types.is_guard);
                                 FStar_Tactics_Types.label =
                                   (g.FStar_Tactics_Types.label)
                               } in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  FStar_Tactics_Monad.monad_tac () ()
                                  FStar_Tactics_Monad.dismiss
                                  (fun uu___4 ->
                                     (fun uu___4 ->
                                        let uu___4 = Obj.magic uu___4 in
                                        let t_eq =
                                          let uu___5 =
                                            let uu___6 =
                                              FStar_Tactics_Types.goal_type g in
                                            env1.FStar_TypeChecker_Env.universe_of
                                              env1 uu___6 in
                                          let uu___6 =
                                            FStar_Tactics_Types.goal_type g in
                                          let uu___7 =
                                            FStar_Tactics_Types.goal_witness
                                              g in
                                          FStar_Syntax_Util.mk_eq2 uu___5
                                            uu___6 u uu___7 in
                                        let uu___5 =
                                          FStar_Tactics_Monad.add_irrelevant_goal
                                            g "dup equation" env1 t_eq
                                            (FStar_Pervasives_Native.Some
                                               goal_sc) in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             FStar_Tactics_Monad.monad_tac ()
                                             () uu___5
                                             (fun uu___6 ->
                                                (fun uu___6 ->
                                                   let uu___6 =
                                                     Obj.magic uu___6 in
                                                   Obj.magic
                                                     (FStar_Tactics_Monad.add_goals
                                                        [g'])) uu___6)))
                                       uu___4))))) uu___2))) uu___1)
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
              let uu___ = f x y in
              if uu___
              then aux (x :: acc) xs ys
              else (acc, (x :: xs), (y :: ys))
          | uu___ -> (acc, l11, l21) in
        let uu___ = aux [] l1 l2 in
        match uu___ with
        | (pr, t1, t2) -> ((FStar_Compiler_List.rev pr), t1, t2)
let (eq_binding :
  FStar_Syntax_Syntax.binding -> FStar_Syntax_Syntax.binding -> Prims.bool) =
  fun b1 -> fun b2 -> false
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal ->
      FStar_Tactics_Types.goal FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g1 ->
         fun g2 ->
           let close_forall_no_univs bs f =
             FStar_Compiler_List.fold_right
               (fun b ->
                  fun f1 ->
                    FStar_Syntax_Util.mk_forall_no_univ
                      b.FStar_Syntax_Syntax.binder_bv f1) bs f in
           let uu___ = FStar_Tactics_Monad.get_phi g1 in
           match uu___ with
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Monad.fail "goal 1 is not irrelevant"))
           | FStar_Pervasives_Native.Some phi1 ->
               Obj.magic
                 (Obj.repr
                    (let uu___1 = FStar_Tactics_Monad.get_phi g2 in
                     match uu___1 with
                     | FStar_Pervasives_Native.None ->
                         Obj.repr
                           (FStar_Tactics_Monad.fail
                              "goal 2 is not irrelevant")
                     | FStar_Pervasives_Native.Some phi2 ->
                         Obj.repr
                           (let gamma1 =
                              (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
                            let gamma2 =
                              (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
                            let uu___2 =
                              longest_prefix eq_binding
                                (FStar_Compiler_List.rev gamma1)
                                (FStar_Compiler_List.rev gamma2) in
                            match uu___2 with
                            | (gamma, r1, r2) ->
                                let t1 =
                                  let uu___3 =
                                    FStar_TypeChecker_Env.binders_of_bindings
                                      (FStar_Compiler_List.rev r1) in
                                  close_forall_no_univs uu___3 phi1 in
                                let t2 =
                                  let uu___3 =
                                    FStar_TypeChecker_Env.binders_of_bindings
                                      (FStar_Compiler_List.rev r2) in
                                  close_forall_no_univs uu___3 phi2 in
                                let goal_sc =
                                  let uu___3 =
                                    let uu___4 = should_check_goal_uvar g1 in
                                    let uu___5 = should_check_goal_uvar g2 in
                                    (uu___4, uu___5) in
                                  match uu___3 with
                                  | (FStar_Syntax_Syntax.Allow_untyped
                                     reason1,
                                     FStar_Syntax_Syntax.Allow_untyped
                                     uu___4) ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Allow_untyped
                                           reason1)
                                  | uu___4 -> FStar_Pervasives_Native.None in
                                let ng = FStar_Syntax_Util.mk_conj t1 t2 in
                                let nenv =
                                  let uu___3 =
                                    FStar_Tactics_Types.goal_env g1 in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___3.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___3.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___3.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (FStar_Compiler_List.rev gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___3.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___3.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___3.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___3.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___3.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.attrtab =
                                      (uu___3.FStar_TypeChecker_Env.attrtab);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___3.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___3.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___3.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___3.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___3.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___3.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq_strict =
                                      (uu___3.FStar_TypeChecker_Env.use_eq_strict);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___3.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___3.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___3.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___3.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.phase1 =
                                      (uu___3.FStar_TypeChecker_Env.phase1);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___3.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___3.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.uvar_subtyping =
                                      (uu___3.FStar_TypeChecker_Env.uvar_subtyping);
                                    FStar_TypeChecker_Env.intactics =
                                      (uu___3.FStar_TypeChecker_Env.intactics);
                                    FStar_TypeChecker_Env.nocoerce =
                                      (uu___3.FStar_TypeChecker_Env.nocoerce);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___3.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                      =
                                      (uu___3.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___3.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                      =
                                      (uu___3.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                    FStar_TypeChecker_Env.teq_nosmt_force =
                                      (uu___3.FStar_TypeChecker_Env.teq_nosmt_force);
                                    FStar_TypeChecker_Env.subtype_nosmt_force
                                      =
                                      (uu___3.FStar_TypeChecker_Env.subtype_nosmt_force);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___3.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___3.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.fv_delta_depths =
                                      (uu___3.FStar_TypeChecker_Env.fv_delta_depths);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___3.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___3.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                      =
                                      (uu___3.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___3.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.mpreprocess =
                                      (uu___3.FStar_TypeChecker_Env.mpreprocess);
                                    FStar_TypeChecker_Env.postprocess =
                                      (uu___3.FStar_TypeChecker_Env.postprocess);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___3.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___3.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___3.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.nbe =
                                      (uu___3.FStar_TypeChecker_Env.nbe);
                                    FStar_TypeChecker_Env.strict_args_tab =
                                      (uu___3.FStar_TypeChecker_Env.strict_args_tab);
                                    FStar_TypeChecker_Env.erasable_types_tab
                                      =
                                      (uu___3.FStar_TypeChecker_Env.erasable_types_tab);
                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                      =
                                      (uu___3.FStar_TypeChecker_Env.enable_defer_to_tac);
                                    FStar_TypeChecker_Env.unif_allow_ref_guards
                                      =
                                      (uu___3.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                    FStar_TypeChecker_Env.erase_erasable_args
                                      =
                                      (uu___3.FStar_TypeChecker_Env.erase_erasable_args);
                                    FStar_TypeChecker_Env.core_check =
                                      (uu___3.FStar_TypeChecker_Env.core_check)
                                  } in
                                let uu___3 =
                                  FStar_Tactics_Monad.mk_irrelevant_goal
                                    "joined" nenv ng goal_sc (rangeof g1)
                                    g1.FStar_Tactics_Types.opts
                                    g1.FStar_Tactics_Types.label in
                                FStar_Class_Monad.op_let_Bang
                                  FStar_Tactics_Monad.monad_tac () ()
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     (fun goal ->
                                        let goal = Obj.magic goal in
                                        let uu___4 =
                                          FStar_Tactics_Monad.if_verbose
                                            (fun uu___5 ->
                                               let uu___6 =
                                                 FStar_Tactics_Printing.goal_to_string_verbose
                                                   g1 in
                                               let uu___7 =
                                                 FStar_Tactics_Printing.goal_to_string_verbose
                                                   g2 in
                                               let uu___8 =
                                                 FStar_Tactics_Printing.goal_to_string_verbose
                                                   goal in
                                               FStar_Compiler_Util.print3
                                                 "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                                 uu___6 uu___7 uu___8) in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             FStar_Tactics_Monad.monad_tac ()
                                             () uu___4
                                             (fun uu___5 ->
                                                (fun uu___5 ->
                                                   let uu___5 =
                                                     Obj.magic uu___5 in
                                                   let uu___6 =
                                                     set_solution g1
                                                       FStar_Syntax_Util.exp_unit in
                                                   Obj.magic
                                                     (FStar_Class_Monad.op_let_Bang
                                                        FStar_Tactics_Monad.monad_tac
                                                        () () uu___6
                                                        (fun uu___7 ->
                                                           (fun uu___7 ->
                                                              let uu___7 =
                                                                Obj.magic
                                                                  uu___7 in
                                                              let uu___8 =
                                                                set_solution
                                                                  g2
                                                                  FStar_Syntax_Util.exp_unit in
                                                              Obj.magic
                                                                (FStar_Class_Monad.op_let_Bang
                                                                   FStar_Tactics_Monad.monad_tac
                                                                   () ()
                                                                   uu___8
                                                                   (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    uu___9 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    goal)))
                                                                    uu___9)))
                                                             uu___7))) uu___5)))
                                       uu___4))))) uu___1 uu___
let (join : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
      (Obj.magic FStar_Tactics_Monad.get)
      (fun uu___1 ->
         (fun ps ->
            let ps = Obj.magic ps in
            match ps.FStar_Tactics_Types.goals with
            | g1::g2::gs ->
                let uu___1 =
                  FStar_Tactics_Monad.set
                    {
                      FStar_Tactics_Types.main_context =
                        (ps.FStar_Tactics_Types.main_context);
                      FStar_Tactics_Types.all_implicits =
                        (ps.FStar_Tactics_Types.all_implicits);
                      FStar_Tactics_Types.goals = gs;
                      FStar_Tactics_Types.smt_goals =
                        (ps.FStar_Tactics_Types.smt_goals);
                      FStar_Tactics_Types.depth =
                        (ps.FStar_Tactics_Types.depth);
                      FStar_Tactics_Types.__dump =
                        (ps.FStar_Tactics_Types.__dump);
                      FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
                      FStar_Tactics_Types.entry_range =
                        (ps.FStar_Tactics_Types.entry_range);
                      FStar_Tactics_Types.guard_policy =
                        (ps.FStar_Tactics_Types.guard_policy);
                      FStar_Tactics_Types.freshness =
                        (ps.FStar_Tactics_Types.freshness);
                      FStar_Tactics_Types.tac_verb_dbg =
                        (ps.FStar_Tactics_Types.tac_verb_dbg);
                      FStar_Tactics_Types.local_state =
                        (ps.FStar_Tactics_Types.local_state);
                      FStar_Tactics_Types.urgency =
                        (ps.FStar_Tactics_Types.urgency)
                    } in
                Obj.magic
                  (FStar_Class_Monad.op_let_Bang
                     FStar_Tactics_Monad.monad_tac () () uu___1
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___2 = Obj.magic uu___2 in
                           let uu___3 = join_goals g1 g2 in
                           Obj.magic
                             (FStar_Class_Monad.op_let_Bang
                                FStar_Tactics_Monad.monad_tac () ()
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun g12 ->
                                      let g12 = Obj.magic g12 in
                                      Obj.magic
                                        (FStar_Tactics_Monad.add_goals [g12]))
                                     uu___4))) uu___2))
            | uu___1 ->
                Obj.magic
                  (FStar_Tactics_Monad.fail "join: less than 2 goals"))
           uu___1)
let (set_options : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    let uu___ =
      FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
        (Obj.magic FStar_Tactics_Monad.cur_goal)
        (fun uu___1 ->
           (fun g ->
              let g = Obj.magic g in
              FStar_Options.push ();
              (let uu___3 =
                 FStar_Compiler_Util.smap_copy g.FStar_Tactics_Types.opts in
               FStar_Options.set uu___3);
              (let res = FStar_Options.set_options s in
               let opts' = FStar_Options.peek () in
               FStar_Options.pop ();
               (match res with
                | FStar_Getopt.Success ->
                    let g' =
                      {
                        FStar_Tactics_Types.goal_main_env =
                          (g.FStar_Tactics_Types.goal_main_env);
                        FStar_Tactics_Types.goal_ctx_uvar =
                          (g.FStar_Tactics_Types.goal_ctx_uvar);
                        FStar_Tactics_Types.opts = opts';
                        FStar_Tactics_Types.is_guard =
                          (g.FStar_Tactics_Types.is_guard);
                        FStar_Tactics_Types.label =
                          (g.FStar_Tactics_Types.label)
                      } in
                    Obj.magic (FStar_Tactics_Monad.replace_cur g')
                | FStar_Getopt.Error err ->
                    Obj.magic (fail2 "Setting options `%s` failed: %s" s err)
                | FStar_Getopt.Help ->
                    Obj.magic
                      (fail1 "Setting options `%s` failed (got `Help`?)" s))))
             uu___1) in
    FStar_Tactics_Monad.wrap_err "set_options" uu___
let (top_env : unit -> env FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            (Obj.magic FStar_Tactics_Monad.get)
            (fun uu___1 ->
               (fun ps ->
                  let ps = Obj.magic ps in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic ps.FStar_Tactics_Types.main_context)))
                 uu___1))) uu___
let (lax_on : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun uu___ ->
       let uu___1 =
         FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
           (Obj.repr ()) in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            uu___1
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___2 = Obj.magic uu___2 in
                  let uu___3 =
                    (FStar_Options.lax ()) ||
                      (FStar_Options.admit_smt_queries ()) in
                  if uu___3
                  then
                    Obj.magic
                      (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                         () (Obj.magic true))
                  else
                    (let uu___5 =
                       FStar_Tactics_Monad.trytac
                         FStar_Tactics_Monad.cur_goal in
                     Obj.magic
                       (FStar_Class_Monad.op_let_Bang
                          FStar_Tactics_Monad.monad_tac () ()
                          (Obj.magic uu___5)
                          (fun uu___6 ->
                             (fun uu___6 ->
                                let uu___6 = Obj.magic uu___6 in
                                match uu___6 with
                                | FStar_Pervasives_Native.Some g ->
                                    let uu___7 =
                                      (let uu___8 =
                                         FStar_Tactics_Types.goal_env g in
                                       uu___8.FStar_TypeChecker_Env.lax) ||
                                        (let uu___8 =
                                           FStar_Tactics_Types.goal_env g in
                                         uu___8.FStar_TypeChecker_Env.admit) in
                                    Obj.magic
                                      (FStar_Class_Monad.return
                                         FStar_Tactics_Monad.monad_tac ()
                                         (Obj.magic uu___7))
                                | FStar_Pervasives_Native.None ->
                                    Obj.magic
                                      (FStar_Class_Monad.return
                                         FStar_Tactics_Monad.monad_tac ()
                                         (Obj.magic false))) uu___6))))
                 uu___2))) uu___
let (unquote :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun tm ->
      let uu___ =
        let uu___1 =
          FStar_Tactics_Monad.if_verbose
            (fun uu___2 ->
               let uu___3 =
                 FStar_Class_Show.show FStar_Syntax_Print.showable_term tm in
               FStar_Compiler_Util.print1 "unquote: tm = %s\n" uu___3) in
        Obj.magic
          (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
             uu___1
             (fun uu___2 ->
                (fun uu___2 ->
                   let uu___2 = Obj.magic uu___2 in
                   Obj.magic
                     (FStar_Class_Monad.op_let_Bang
                        FStar_Tactics_Monad.monad_tac () ()
                        (Obj.magic FStar_Tactics_Monad.cur_goal)
                        (fun uu___3 ->
                           (fun goal ->
                              let goal = Obj.magic goal in
                              let env1 =
                                let uu___3 =
                                  FStar_Tactics_Types.goal_env goal in
                                FStar_TypeChecker_Env.set_expected_typ uu___3
                                  ty in
                              let uu___3 = __tc_ghost env1 tm in
                              Obj.magic
                                (FStar_Class_Monad.op_let_Bang
                                   FStar_Tactics_Monad.monad_tac () ()
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun uu___4 ->
                                         let uu___4 = Obj.magic uu___4 in
                                         match uu___4 with
                                         | (tm1, typ, guard) ->
                                             let uu___5 =
                                               FStar_Tactics_Monad.if_verbose
                                                 (fun uu___6 ->
                                                    let uu___7 =
                                                      FStar_Class_Show.show
                                                        FStar_Syntax_Print.showable_term
                                                        tm1 in
                                                    FStar_Compiler_Util.print1
                                                      "unquote: tm' = %s\n"
                                                      uu___7) in
                                             Obj.magic
                                               (FStar_Class_Monad.op_let_Bang
                                                  FStar_Tactics_Monad.monad_tac
                                                  () () uu___5
                                                  (fun uu___6 ->
                                                     (fun uu___6 ->
                                                        let uu___6 =
                                                          Obj.magic uu___6 in
                                                        let uu___7 =
                                                          FStar_Tactics_Monad.if_verbose
                                                            (fun uu___8 ->
                                                               let uu___9 =
                                                                 FStar_Class_Show.show
                                                                   FStar_Syntax_Print.showable_term
                                                                   typ in
                                                               FStar_Compiler_Util.print1
                                                                 "unquote: typ = %s\n"
                                                                 uu___9) in
                                                        Obj.magic
                                                          (FStar_Class_Monad.op_let_Bang
                                                             FStar_Tactics_Monad.monad_tac
                                                             () () uu___7
                                                             (fun uu___8 ->
                                                                (fun uu___8
                                                                   ->
                                                                   let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    uu___8 in
                                                                   let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    should_check_goal_uvar
                                                                    goal in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___11 in
                                                                    proc_guard
                                                                    "unquote"
                                                                    env1
                                                                    guard
                                                                    uu___10
                                                                    (rangeof
                                                                    goal) in
                                                                   Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___9
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    uu___10 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    tm1)))
                                                                    uu___10)))
                                                                  uu___8)))
                                                       uu___6))) uu___4)))
                             uu___3))) uu___2)) in
      FStar_Tactics_Monad.wrap_err "unquote" uu___
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env1 ->
         fun ty ->
           Obj.magic
             (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                () (Obj.magic FStar_Tactics_Monad.get)
                (fun uu___ ->
                   (fun ps ->
                      let ps = Obj.magic ps in
                      let uu___ =
                        match ty with
                        | FStar_Pervasives_Native.Some ty1 ->
                            let env2 =
                              let uu___1 =
                                let uu___2 = FStar_Syntax_Util.type_u () in
                                FStar_Pervasives_Native.fst uu___2 in
                              FStar_TypeChecker_Env.set_expected_typ env1
                                uu___1 in
                            let uu___1 = __tc_ghost env2 ty1 in
                            Obj.magic
                              (FStar_Class_Monad.op_let_Bang
                                 FStar_Tactics_Monad.monad_tac () ()
                                 (Obj.magic uu___1)
                                 (fun uu___2 ->
                                    (fun uu___2 ->
                                       let uu___2 = Obj.magic uu___2 in
                                       match uu___2 with
                                       | (ty2, uu___3, g) ->
                                           Obj.magic
                                             (FStar_Class_Monad.return
                                                FStar_Tactics_Monad.monad_tac
                                                ()
                                                (Obj.magic
                                                   (ty2, g,
                                                     (ty2.FStar_Syntax_Syntax.pos)))))
                                      uu___2))
                        | FStar_Pervasives_Native.None ->
                            let uu___1 =
                              let uu___2 =
                                let uu___3 = FStar_Syntax_Util.type_u () in
                                FStar_Pervasives_Native.fst uu___3 in
                              FStar_Tactics_Monad.new_uvar "uvar_env.2" env1
                                uu___2 FStar_Pervasives_Native.None []
                                ps.FStar_Tactics_Types.entry_range in
                            Obj.magic
                              (FStar_Class_Monad.op_let_Bang
                                 FStar_Tactics_Monad.monad_tac () ()
                                 (Obj.magic uu___1)
                                 (fun uu___2 ->
                                    (fun uu___2 ->
                                       let uu___2 = Obj.magic uu___2 in
                                       match uu___2 with
                                       | (typ, uvar_typ) ->
                                           Obj.magic
                                             (FStar_Class_Monad.return
                                                FStar_Tactics_Monad.monad_tac
                                                ()
                                                (Obj.magic
                                                   (typ,
                                                     FStar_TypeChecker_Env.trivial_guard,
                                                     FStar_Compiler_Range_Type.dummyRange))))
                                      uu___2)) in
                      Obj.magic
                        (FStar_Class_Monad.op_let_Bang
                           FStar_Tactics_Monad.monad_tac () ()
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 let uu___1 = Obj.magic uu___1 in
                                 match uu___1 with
                                 | (typ, g, r) ->
                                     let uu___2 =
                                       proc_guard "uvar_env_typ" env1 g
                                         FStar_Pervasives_Native.None r in
                                     Obj.magic
                                       (FStar_Class_Monad.op_let_Bang
                                          FStar_Tactics_Monad.monad_tac () ()
                                          uu___2
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                let uu___3 = Obj.magic uu___3 in
                                                let uu___4 =
                                                  FStar_Tactics_Monad.new_uvar
                                                    "uvar_env" env1 typ
                                                    FStar_Pervasives_Native.None
                                                    []
                                                    ps.FStar_Tactics_Types.entry_range in
                                                Obj.magic
                                                  (FStar_Class_Monad.op_let_Bang
                                                     FStar_Tactics_Monad.monad_tac
                                                     () () (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        (fun uu___5 ->
                                                           let uu___5 =
                                                             Obj.magic uu___5 in
                                                           match uu___5 with
                                                           | (t, uvar_t) ->
                                                               Obj.magic
                                                                 (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (
                                                                    Obj.magic
                                                                    t)))
                                                          uu___5))) uu___3)))
                                uu___1))) uu___))) uu___1 uu___
let (ghost_uvar_env :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env1 ->
         fun ty ->
           Obj.magic
             (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                () (Obj.magic FStar_Tactics_Monad.get)
                (fun uu___ ->
                   (fun ps ->
                      let ps = Obj.magic ps in
                      let uu___ = __tc_ghost env1 ty in
                      Obj.magic
                        (FStar_Class_Monad.op_let_Bang
                           FStar_Tactics_Monad.monad_tac () ()
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 let uu___1 = Obj.magic uu___1 in
                                 match uu___1 with
                                 | (typ, uu___2, g) ->
                                     let uu___3 =
                                       proc_guard "ghost_uvar_env_typ" env1 g
                                         FStar_Pervasives_Native.None
                                         ty.FStar_Syntax_Syntax.pos in
                                     Obj.magic
                                       (FStar_Class_Monad.op_let_Bang
                                          FStar_Tactics_Monad.monad_tac () ()
                                          uu___3
                                          (fun uu___4 ->
                                             (fun uu___4 ->
                                                let uu___4 = Obj.magic uu___4 in
                                                let uu___5 =
                                                  FStar_Tactics_Monad.new_uvar
                                                    "uvar_env" env1 typ
                                                    (FStar_Pervasives_Native.Some
                                                       (FStar_Syntax_Syntax.Allow_ghost
                                                          "User ghost uvar"))
                                                    []
                                                    ps.FStar_Tactics_Types.entry_range in
                                                Obj.magic
                                                  (FStar_Class_Monad.op_let_Bang
                                                     FStar_Tactics_Monad.monad_tac
                                                     () () (Obj.magic uu___5)
                                                     (fun uu___6 ->
                                                        (fun uu___6 ->
                                                           let uu___6 =
                                                             Obj.magic uu___6 in
                                                           match uu___6 with
                                                           | (t, uvar_t) ->
                                                               Obj.magic
                                                                 (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (
                                                                    Obj.magic
                                                                    t)))
                                                          uu___6))) uu___4)))
                                uu___1))) uu___))) uu___1 uu___
let (fresh_universe_uvar :
  unit -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun uu___ ->
       let uu___1 =
         let uu___2 = FStar_Syntax_Util.type_u () in
         FStar_Pervasives_Native.fst uu___2 in
       Obj.magic
         (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
            (Obj.magic uu___1))) uu___
let (unshelve : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu___ =
      FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
        (Obj.magic FStar_Tactics_Monad.get)
        (fun uu___1 ->
           (fun ps ->
              let ps = Obj.magic ps in
              let env1 = ps.FStar_Tactics_Types.main_context in
              let opts =
                match ps.FStar_Tactics_Types.goals with
                | g::uu___1 -> g.FStar_Tactics_Types.opts
                | uu___1 -> FStar_Options.peek () in
              let uu___1 = FStar_Syntax_Util.head_and_args t in
              match uu___1 with
              | ({
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                     (ctx_uvar, uu___2);
                   FStar_Syntax_Syntax.pos = uu___3;
                   FStar_Syntax_Syntax.vars = uu___4;
                   FStar_Syntax_Syntax.hash_code = uu___5;_},
                 uu___6) ->
                  let env2 =
                    {
                      FStar_TypeChecker_Env.solver =
                        (env1.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (env1.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (env1.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (env1.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (env1.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (env1.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (env1.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (env1.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (env1.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (env1.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (env1.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (env1.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (env1.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (env1.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (env1.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (env1.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (env1.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (env1.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (env1.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (env1.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (env1.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (env1.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (env1.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (env1.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.intactics =
                        (env1.FStar_TypeChecker_Env.intactics);
                      FStar_TypeChecker_Env.nocoerce =
                        (env1.FStar_TypeChecker_Env.nocoerce);
                      FStar_TypeChecker_Env.tc_term =
                        (env1.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                        (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                      FStar_TypeChecker_Env.universe_of =
                        (env1.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                        =
                        (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                      FStar_TypeChecker_Env.teq_nosmt_force =
                        (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                      FStar_TypeChecker_Env.subtype_nosmt_force =
                        (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (env1.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (env1.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (env1.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (env1.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (env1.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (env1.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (env1.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.identifier_info =
                        (env1.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (env1.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (env1.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (env1.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (env1.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (env1.FStar_TypeChecker_Env.erasable_types_tab);
                      FStar_TypeChecker_Env.enable_defer_to_tac =
                        (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                      FStar_TypeChecker_Env.unif_allow_ref_guards =
                        (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                      FStar_TypeChecker_Env.erase_erasable_args =
                        (env1.FStar_TypeChecker_Env.erase_erasable_args);
                      FStar_TypeChecker_Env.core_check =
                        (env1.FStar_TypeChecker_Env.core_check)
                    } in
                  let g =
                    FStar_Tactics_Types.mk_goal env2 ctx_uvar opts false "" in
                  let g1 = bnorm_goal g in
                  Obj.magic (FStar_Tactics_Monad.add_goals [g1])
              | uu___2 -> Obj.magic (FStar_Tactics_Monad.fail "not a uvar"))
             uu___1) in
    FStar_Tactics_Monad.wrap_err "unshelve" uu___
let (tac_and :
  Prims.bool FStar_Tactics_Monad.tac ->
    Prims.bool FStar_Tactics_Monad.tac -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t1 ->
         fun t2 ->
           Obj.magic
             (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                () (Obj.magic t1)
                (fun uu___ ->
                   (fun uu___ ->
                      let uu___ = Obj.magic uu___ in
                      if uu___
                      then Obj.magic (Obj.repr t2)
                      else
                        Obj.magic
                          (Obj.repr
                             (FStar_Class_Monad.return
                                FStar_Tactics_Monad.monad_tac ()
                                (Obj.magic false)))) uu___))) uu___1 uu___
let default_if_err :
  'a . 'a -> 'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac =
  fun uu___1 ->
    fun uu___ ->
      (fun def ->
         fun t ->
           let uu___ = FStar_Tactics_Monad.catch t in
           Obj.magic
             (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                () (Obj.magic uu___)
                (fun uu___1 ->
                   (fun r ->
                      let r = Obj.magic r in
                      match r with
                      | FStar_Pervasives.Inl uu___1 ->
                          Obj.magic
                            (FStar_Class_Monad.return
                               FStar_Tactics_Monad.monad_tac ()
                               (Obj.magic def))
                      | FStar_Pervasives.Inr v ->
                          Obj.magic
                            (FStar_Class_Monad.return
                               FStar_Tactics_Monad.monad_tac () (Obj.magic v)))
                     uu___1))) uu___1 uu___
let (match_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          Obj.magic
            (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
               () (Obj.magic FStar_Tactics_Monad.get)
               (fun uu___1 ->
                  (fun ps ->
                     let ps = Obj.magic ps in
                     let uu___1 = __tc e t1 in
                     Obj.magic
                       (FStar_Class_Monad.op_let_Bang
                          FStar_Tactics_Monad.monad_tac () ()
                          (Obj.magic uu___1)
                          (fun uu___2 ->
                             (fun uu___2 ->
                                let uu___2 = Obj.magic uu___2 in
                                match uu___2 with
                                | (t11, ty1, g1) ->
                                    let uu___3 = __tc e t2 in
                                    Obj.magic
                                      (FStar_Class_Monad.op_let_Bang
                                         FStar_Tactics_Monad.monad_tac () ()
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            (fun uu___4 ->
                                               let uu___4 = Obj.magic uu___4 in
                                               match uu___4 with
                                               | (t21, ty2, g2) ->
                                                   let uu___5 =
                                                     proc_guard
                                                       "match_env g1" e g1
                                                       FStar_Pervasives_Native.None
                                                       ps.FStar_Tactics_Types.entry_range in
                                                   Obj.magic
                                                     (FStar_Class_Monad.op_let_Bang
                                                        FStar_Tactics_Monad.monad_tac
                                                        () () uu___5
                                                        (fun uu___6 ->
                                                           (fun uu___6 ->
                                                              let uu___6 =
                                                                Obj.magic
                                                                  uu___6 in
                                                              let uu___7 =
                                                                proc_guard
                                                                  "match_env g2"
                                                                  e g2
                                                                  FStar_Pervasives_Native.None
                                                                  ps.FStar_Tactics_Types.entry_range in
                                                              Obj.magic
                                                                (FStar_Class_Monad.op_let_Bang
                                                                   FStar_Tactics_Monad.monad_tac
                                                                   () ()
                                                                   uu___7
                                                                   (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    uu___8 in
                                                                    let must_tot
                                                                    = true in
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    do_match
                                                                    must_tot
                                                                    e ty1 ty2 in
                                                                    let uu___11
                                                                    =
                                                                    do_match
                                                                    must_tot
                                                                    e t11 t21 in
                                                                    tac_and
                                                                    uu___10
                                                                    uu___11 in
                                                                    Obj.magic
                                                                    (default_if_err
                                                                    false
                                                                    uu___9))
                                                                    uu___8)))
                                                             uu___6))) uu___4)))
                               uu___2))) uu___1)) in
        FStar_Tactics_Monad.wrap_err "match_env" uu___
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          Obj.magic
            (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
               () (Obj.magic FStar_Tactics_Monad.get)
               (fun uu___1 ->
                  (fun ps ->
                     let ps = Obj.magic ps in
                     let uu___1 = __tc e t1 in
                     Obj.magic
                       (FStar_Class_Monad.op_let_Bang
                          FStar_Tactics_Monad.monad_tac () ()
                          (Obj.magic uu___1)
                          (fun uu___2 ->
                             (fun uu___2 ->
                                let uu___2 = Obj.magic uu___2 in
                                match uu___2 with
                                | (t11, ty1, g1) ->
                                    let uu___3 = __tc e t2 in
                                    Obj.magic
                                      (FStar_Class_Monad.op_let_Bang
                                         FStar_Tactics_Monad.monad_tac () ()
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            (fun uu___4 ->
                                               let uu___4 = Obj.magic uu___4 in
                                               match uu___4 with
                                               | (t21, ty2, g2) ->
                                                   let uu___5 =
                                                     proc_guard
                                                       "unify_env g1" e g1
                                                       FStar_Pervasives_Native.None
                                                       ps.FStar_Tactics_Types.entry_range in
                                                   Obj.magic
                                                     (FStar_Class_Monad.op_let_Bang
                                                        FStar_Tactics_Monad.monad_tac
                                                        () () uu___5
                                                        (fun uu___6 ->
                                                           (fun uu___6 ->
                                                              let uu___6 =
                                                                Obj.magic
                                                                  uu___6 in
                                                              let uu___7 =
                                                                proc_guard
                                                                  "unify_env g2"
                                                                  e g2
                                                                  FStar_Pervasives_Native.None
                                                                  ps.FStar_Tactics_Types.entry_range in
                                                              Obj.magic
                                                                (FStar_Class_Monad.op_let_Bang
                                                                   FStar_Tactics_Monad.monad_tac
                                                                   () ()
                                                                   uu___7
                                                                   (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    uu___8 in
                                                                    let must_tot
                                                                    = true in
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    do_unify
                                                                    must_tot
                                                                    e ty1 ty2 in
                                                                    let uu___11
                                                                    =
                                                                    do_unify
                                                                    must_tot
                                                                    e t11 t21 in
                                                                    tac_and
                                                                    uu___10
                                                                    uu___11 in
                                                                    Obj.magic
                                                                    (default_if_err
                                                                    false
                                                                    uu___9))
                                                                    uu___8)))
                                                             uu___6))) uu___4)))
                               uu___2))) uu___1)) in
        FStar_Tactics_Monad.wrap_err "unify_env" uu___
let (unify_guard_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          Obj.magic
            (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
               () (Obj.magic FStar_Tactics_Monad.get)
               (fun uu___1 ->
                  (fun ps ->
                     let ps = Obj.magic ps in
                     let uu___1 = __tc e t1 in
                     Obj.magic
                       (FStar_Class_Monad.op_let_Bang
                          FStar_Tactics_Monad.monad_tac () ()
                          (Obj.magic uu___1)
                          (fun uu___2 ->
                             (fun uu___2 ->
                                let uu___2 = Obj.magic uu___2 in
                                match uu___2 with
                                | (t11, ty1, g1) ->
                                    let uu___3 = __tc e t2 in
                                    Obj.magic
                                      (FStar_Class_Monad.op_let_Bang
                                         FStar_Tactics_Monad.monad_tac () ()
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            (fun uu___4 ->
                                               let uu___4 = Obj.magic uu___4 in
                                               match uu___4 with
                                               | (t21, ty2, g2) ->
                                                   let uu___5 =
                                                     proc_guard
                                                       "unify_guard_env g1" e
                                                       g1
                                                       FStar_Pervasives_Native.None
                                                       ps.FStar_Tactics_Types.entry_range in
                                                   Obj.magic
                                                     (FStar_Class_Monad.op_let_Bang
                                                        FStar_Tactics_Monad.monad_tac
                                                        () () uu___5
                                                        (fun uu___6 ->
                                                           (fun uu___6 ->
                                                              let uu___6 =
                                                                Obj.magic
                                                                  uu___6 in
                                                              let uu___7 =
                                                                proc_guard
                                                                  "unify_guard_env g2"
                                                                  e g2
                                                                  FStar_Pervasives_Native.None
                                                                  ps.FStar_Tactics_Types.entry_range in
                                                              Obj.magic
                                                                (FStar_Class_Monad.op_let_Bang
                                                                   FStar_Tactics_Monad.monad_tac
                                                                   () ()
                                                                   uu___7
                                                                   (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    uu___8 in
                                                                    let must_tot
                                                                    = true in
                                                                    let uu___9
                                                                    =
                                                                    do_unify_maybe_guards
                                                                    true
                                                                    must_tot
                                                                    e ty1 ty2 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    uu___10 in
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    false))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g11 ->
                                                                    let uu___11
                                                                    =
                                                                    do_unify_maybe_guards
                                                                    true
                                                                    must_tot
                                                                    e t11 t21 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    uu___12 in
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    false))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g21 ->
                                                                    let formula
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    guard_formula
                                                                    g11 in
                                                                    let uu___14
                                                                    =
                                                                    guard_formula
                                                                    g21 in
                                                                    FStar_Syntax_Util.mk_conj
                                                                    uu___13
                                                                    uu___14 in
                                                                    let uu___13
                                                                    =
                                                                    FStar_Tactics_Monad.goal_of_guard
                                                                    "unify_guard_env.g2"
                                                                    e formula
                                                                    FStar_Pervasives_Native.None
                                                                    ps.FStar_Tactics_Types.entry_range in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun goal
                                                                    ->
                                                                    let goal
                                                                    =
                                                                    Obj.magic
                                                                    goal in
                                                                    let uu___14
                                                                    =
                                                                    FStar_Tactics_Monad.push_goals
                                                                    [goal] in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___14
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    Obj.magic
                                                                    uu___15 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    true)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                             uu___6))) uu___4)))
                               uu___2))) uu___1)) in
        FStar_Tactics_Monad.wrap_err "unify_guard_env" uu___
let (launch_process :
  Prims.string ->
    Prims.string Prims.list ->
      Prims.string -> Prims.string FStar_Tactics_Monad.tac)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun prog ->
           fun args ->
             fun input ->
               let uu___ =
                 FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                   (Obj.repr ()) in
               Obj.magic
                 (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac
                    () () uu___
                    (fun uu___1 ->
                       (fun uu___1 ->
                          let uu___1 = Obj.magic uu___1 in
                          let uu___2 = FStar_Options.unsafe_tactic_exec () in
                          if uu___2
                          then
                            Obj.magic
                              (Obj.repr
                                 (let s =
                                    FStar_Compiler_Util.run_process
                                      "tactic_launch" prog args
                                      (FStar_Pervasives_Native.Some input) in
                                  FStar_Class_Monad.return
                                    FStar_Tactics_Monad.monad_tac ()
                                    (Obj.magic s)))
                          else
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Monad.fail
                                    "launch_process: will not run anything unless --unsafe_tactic_exec is provided")))
                         uu___1))) uu___2 uu___1 uu___
let (fresh_bv_named :
  Prims.string -> FStar_Syntax_Syntax.bv FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun nm ->
       let uu___ =
         FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
           (Obj.repr ()) in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            uu___
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___1 = Obj.magic uu___1 in
                  let uu___2 =
                    FStar_Syntax_Syntax.gen_bv nm
                      FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic uu___2))) uu___1))) uu___
let (change : FStar_Syntax_Syntax.typ -> unit FStar_Tactics_Monad.tac) =
  fun ty ->
    let uu___ =
      let uu___1 =
        FStar_Tactics_Monad.if_verbose
          (fun uu___2 ->
             let uu___3 =
               FStar_Class_Show.show FStar_Syntax_Print.showable_term ty in
             FStar_Compiler_Util.print1 "change: ty = %s\n" uu___3) in
      FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
        uu___1
        (fun uu___2 ->
           (fun uu___2 ->
              let uu___2 = Obj.magic uu___2 in
              Obj.magic
                (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac
                   () () (Obj.magic FStar_Tactics_Monad.cur_goal)
                   (fun uu___3 ->
                      (fun g ->
                         let g = Obj.magic g in
                         let uu___3 =
                           let uu___4 = FStar_Tactics_Types.goal_env g in
                           __tc uu___4 ty in
                         Obj.magic
                           (FStar_Class_Monad.op_let_Bang
                              FStar_Tactics_Monad.monad_tac () ()
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun uu___4 ->
                                    let uu___4 = Obj.magic uu___4 in
                                    match uu___4 with
                                    | (ty1, uu___5, guard) ->
                                        let uu___6 =
                                          let uu___7 =
                                            FStar_Tactics_Types.goal_env g in
                                          let uu___8 =
                                            let uu___9 =
                                              should_check_goal_uvar g in
                                            FStar_Pervasives_Native.Some
                                              uu___9 in
                                          proc_guard "change" uu___7 guard
                                            uu___8 (rangeof g) in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             FStar_Tactics_Monad.monad_tac ()
                                             () uu___6
                                             (fun uu___7 ->
                                                (fun uu___7 ->
                                                   let uu___7 =
                                                     Obj.magic uu___7 in
                                                   let must_tot = true in
                                                   let uu___8 =
                                                     let uu___9 =
                                                       FStar_Tactics_Types.goal_env
                                                         g in
                                                     let uu___10 =
                                                       FStar_Tactics_Types.goal_type
                                                         g in
                                                     do_unify must_tot uu___9
                                                       uu___10 ty1 in
                                                   Obj.magic
                                                     (FStar_Class_Monad.op_let_Bang
                                                        FStar_Tactics_Monad.monad_tac
                                                        () ()
                                                        (Obj.magic uu___8)
                                                        (fun uu___9 ->
                                                           (fun bb ->
                                                              let bb =
                                                                Obj.magic bb in
                                                              if bb
                                                              then
                                                                let uu___9 =
                                                                  FStar_Tactics_Monad.goal_with_type
                                                                    g ty1 in
                                                                Obj.magic
                                                                  (FStar_Tactics_Monad.replace_cur
                                                                    uu___9)
                                                              else
                                                                (let steps =
                                                                   [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                                                   FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant;
                                                                   FStar_TypeChecker_Env.Primops] in
                                                                 let ng =
                                                                   let uu___10
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                   let uu___11
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g in
                                                                   normalize
                                                                    steps
                                                                    uu___10
                                                                    uu___11 in
                                                                 let nty =
                                                                   let uu___10
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                   normalize
                                                                    steps
                                                                    uu___10
                                                                    ty1 in
                                                                 let uu___10
                                                                   =
                                                                   let uu___11
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                   do_unify
                                                                    must_tot
                                                                    uu___11
                                                                    ng nty in
                                                                 Obj.magic
                                                                   (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun b ->
                                                                    let b =
                                                                    Obj.magic
                                                                    b in
                                                                    if b
                                                                    then
                                                                    let uu___11
                                                                    =
                                                                    FStar_Tactics_Monad.goal_with_type
                                                                    g ty1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Monad.replace_cur
                                                                    uu___11)
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Monad.fail
                                                                    "not convertible"))
                                                                    uu___11))))
                                                             uu___9))) uu___7)))
                                   uu___4))) uu___3))) uu___2) in
    FStar_Tactics_Monad.wrap_err "change" uu___
let (failwhen : Prims.bool -> Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    fun msg ->
      if b
      then FStar_Tactics_Monad.fail msg
      else
        FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
          (Obj.repr ())
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list
      FStar_Tactics_Monad.tac)
  =
  fun s_tm ->
    let uu___ =
      Obj.magic
        (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
           (Obj.magic FStar_Tactics_Monad.cur_goal)
           (fun uu___1 ->
              (fun g ->
                 let g = Obj.magic g in
                 let uu___1 =
                   let uu___2 = FStar_Tactics_Types.goal_env g in
                   __tc uu___2 s_tm in
                 Obj.magic
                   (FStar_Class_Monad.op_let_Bang
                      FStar_Tactics_Monad.monad_tac () () (Obj.magic uu___1)
                      (fun uu___2 ->
                         (fun uu___2 ->
                            let uu___2 = Obj.magic uu___2 in
                            match uu___2 with
                            | (s_tm1, s_ty, guard) ->
                                let uu___3 =
                                  let uu___4 = FStar_Tactics_Types.goal_env g in
                                  let uu___5 =
                                    let uu___6 = should_check_goal_uvar g in
                                    FStar_Pervasives_Native.Some uu___6 in
                                  proc_guard "destruct" uu___4 guard uu___5
                                    (rangeof g) in
                                Obj.magic
                                  (FStar_Class_Monad.op_let_Bang
                                     FStar_Tactics_Monad.monad_tac () ()
                                     uu___3
                                     (fun uu___4 ->
                                        (fun uu___4 ->
                                           let uu___4 = Obj.magic uu___4 in
                                           let s_ty1 =
                                             let uu___5 =
                                               FStar_Tactics_Types.goal_env g in
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.UnfoldTac;
                                               FStar_TypeChecker_Env.Weak;
                                               FStar_TypeChecker_Env.HNF;
                                               FStar_TypeChecker_Env.UnfoldUntil
                                                 FStar_Syntax_Syntax.delta_constant]
                                               uu___5 s_ty in
                                           let uu___5 =
                                             let uu___6 =
                                               FStar_Syntax_Util.unrefine
                                                 s_ty1 in
                                             FStar_Syntax_Util.head_and_args_full
                                               uu___6 in
                                           match uu___5 with
                                           | (h, args) ->
                                               let uu___6 =
                                                 let uu___7 =
                                                   let uu___8 =
                                                     FStar_Syntax_Subst.compress
                                                       h in
                                                   uu___8.FStar_Syntax_Syntax.n in
                                                 match uu___7 with
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     fv ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Class_Monad.return
                                                             FStar_Tactics_Monad.monad_tac
                                                             ()
                                                             (Obj.magic
                                                                (fv, []))))
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     (h', us) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (let uu___8 =
                                                             let uu___9 =
                                                               FStar_Syntax_Subst.compress
                                                                 h' in
                                                             uu___9.FStar_Syntax_Syntax.n in
                                                           match uu___8 with
                                                           | FStar_Syntax_Syntax.Tm_fvar
                                                               fv ->
                                                               Obj.repr
                                                                 (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (
                                                                    Obj.magic
                                                                    (fv, us)))
                                                           | uu___9 ->
                                                               Obj.repr
                                                                 (FStar_Compiler_Effect.failwith
                                                                    "impossible: uinst over something that's not an fvar")))
                                                 | uu___8 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Monad.fail
                                                             "type is not an fv")) in
                                               Obj.magic
                                                 (FStar_Class_Monad.op_let_Bang
                                                    FStar_Tactics_Monad.monad_tac
                                                    () () (Obj.magic uu___6)
                                                    (fun uu___7 ->
                                                       (fun uu___7 ->
                                                          let uu___7 =
                                                            Obj.magic uu___7 in
                                                          match uu___7 with
                                                          | (fv, a_us) ->
                                                              let t_lid =
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                                  fv in
                                                              let uu___8 =
                                                                let uu___9 =
                                                                  FStar_Tactics_Types.goal_env
                                                                    g in
                                                                FStar_TypeChecker_Env.lookup_sigelt
                                                                  uu___9
                                                                  t_lid in
                                                              (match uu___8
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                   ->
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Monad.fail
                                                                    "type not found in environment"))
                                                               | FStar_Pervasives_Native.Some
                                                                   se ->
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    se.FStar_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Sig_inductive_typ
                                                                    {
                                                                    FStar_Syntax_Syntax.lid
                                                                    = uu___9;
                                                                    FStar_Syntax_Syntax.us
                                                                    = t_us;
                                                                    FStar_Syntax_Syntax.params
                                                                    = t_ps;
                                                                    FStar_Syntax_Syntax.num_uniform_params
                                                                    = uu___10;
                                                                    FStar_Syntax_Syntax.t
                                                                    = t_ty;
                                                                    FStar_Syntax_Syntax.mutuals
                                                                    = mut;
                                                                    FStar_Syntax_Syntax.ds
                                                                    = c_lids;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let erasable
                                                                    =
                                                                    FStar_Syntax_Util.has_attribute
                                                                    se.FStar_Syntax_Syntax.sigattrs
                                                                    FStar_Parser_Const.erasable_attr in
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    erasable
                                                                    &&
                                                                    (let uu___13
                                                                    =
                                                                    FStar_Tactics_Monad.is_irrelevant
                                                                    g in
                                                                    Prims.op_Negation
                                                                    uu___13) in
                                                                    failwhen
                                                                    uu___12
                                                                    "cannot destruct erasable type to solve proof-relevant goal" in
                                                                    FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___11
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    uu___12 in
                                                                    let uu___13
                                                                    =
                                                                    failwhen
                                                                    ((FStar_Compiler_List.length
                                                                    a_us) <>
                                                                    (FStar_Compiler_List.length
                                                                    t_us))
                                                                    "t_us don't match?" in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___13
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    uu___14 in
                                                                    let uu___15
                                                                    =
                                                                    FStar_Syntax_Subst.open_term
                                                                    t_ps t_ty in
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    (t_ps1,
                                                                    t_ty1) ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.mapM
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    c_lid ->
                                                                    let c_lid
                                                                    =
                                                                    Obj.magic
                                                                    c_lid in
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu___18
                                                                    c_lid in
                                                                    match uu___17
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Monad.fail
                                                                    "ctor not found?"))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    se1.FStar_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Sig_datacon
                                                                    {
                                                                    FStar_Syntax_Syntax.lid1
                                                                    = uu___18;
                                                                    FStar_Syntax_Syntax.us1
                                                                    = c_us;
                                                                    FStar_Syntax_Syntax.t1
                                                                    = c_ty;
                                                                    FStar_Syntax_Syntax.ty_lid
                                                                    = uu___19;
                                                                    FStar_Syntax_Syntax.num_ty_params
                                                                    = nparam;
                                                                    FStar_Syntax_Syntax.mutuals1
                                                                    = mut1;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let qual
                                                                    =
                                                                    let fallback
                                                                    uu___20 =
                                                                    FStar_Pervasives_Native.Some
                                                                    FStar_Syntax_Syntax.Data_ctor in
                                                                    let qninfo
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    FStar_TypeChecker_Env.lookup_qname
                                                                    uu___20
                                                                    c_lid in
                                                                    match qninfo
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Inr
                                                                    (se2,
                                                                    _us),
                                                                    _rng) ->
                                                                    FStar_Syntax_DsEnv.fv_qual_of_se
                                                                    se2
                                                                    | 
                                                                    uu___20
                                                                    ->
                                                                    fallback
                                                                    () in
                                                                    let fv1 =
                                                                    FStar_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    qual in
                                                                    let uu___20
                                                                    =
                                                                    failwhen
                                                                    ((FStar_Compiler_List.length
                                                                    a_us) <>
                                                                    (FStar_Compiler_List.length
                                                                    c_us))
                                                                    "t_us don't match?" in
                                                                    FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___20
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    Obj.magic
                                                                    uu___21 in
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty in
                                                                    let uu___22
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1) in
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    (c_us1,
                                                                    c_ty2) ->
                                                                    let uu___23
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2 in
                                                                    (match uu___23
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    comp) ->
                                                                    let uu___24
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname in
                                                                    let ppname1
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStar_Class_Show.show
                                                                    FStar_Ident.showable_ident
                                                                    ppname in
                                                                    Prims.strcat
                                                                    "a"
                                                                    uu___27 in
                                                                    let uu___27
                                                                    =
                                                                    FStar_Ident.range_of_id
                                                                    ppname in
                                                                    (uu___26,
                                                                    uu___27) in
                                                                    FStar_Ident.mk_ident
                                                                    uu___25 in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (bv.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (bv.FStar_Syntax_Syntax.sort)
                                                                    } in
                                                                    let bs' =
                                                                    FStar_Compiler_List.map
                                                                    (fun b ->
                                                                    let uu___25
                                                                    =
                                                                    rename_bv
                                                                    b.FStar_Syntax_Syntax.binder_bv in
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = uu___25;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    =
                                                                    (b.FStar_Syntax_Syntax.binder_qual);
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    =
                                                                    (b.FStar_Syntax_Syntax.binder_positivity);
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    =
                                                                    (b.FStar_Syntax_Syntax.binder_attrs)
                                                                    }) bs in
                                                                    let subst
                                                                    =
                                                                    FStar_Compiler_List.map2
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    fun
                                                                    uu___26
                                                                    ->
                                                                    match 
                                                                    (uu___25,
                                                                    uu___26)
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___27;
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    = uu___28;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___29;_},
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv';
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___30;
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    = uu___31;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___32;_})
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv' in
                                                                    (bv,
                                                                    uu___34) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu___33)
                                                                    bs bs' in
                                                                    let uu___25
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs' in
                                                                    let uu___26
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst
                                                                    comp in
                                                                    (uu___25,
                                                                    uu___26) in
                                                                    (match uu___24
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    comp1) ->
                                                                    let uu___25
                                                                    =
                                                                    FStar_Compiler_List.splitAt
                                                                    nparam
                                                                    bs1 in
                                                                    (match uu___25
                                                                    with
                                                                    | 
                                                                    (d_ps,
                                                                    bs2) ->
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1 in
                                                                    Prims.op_Negation
                                                                    uu___28 in
                                                                    failwhen
                                                                    uu___27
                                                                    "not total?" in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___26
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    Obj.magic
                                                                    uu___27 in
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
                                                                    uu___28 =
                                                                    match uu___28
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu___29)
                                                                    -> true
                                                                    | 
                                                                    uu___29
                                                                    -> false in
                                                                    let uu___28
                                                                    =
                                                                    FStar_Compiler_List.splitAt
                                                                    nparam
                                                                    args in
                                                                    match uu___28
                                                                    with
                                                                    | 
                                                                    (a_ps,
                                                                    a_is) ->
                                                                    let uu___29
                                                                    =
                                                                    failwhen
                                                                    ((FStar_Compiler_List.length
                                                                    a_ps) <>
                                                                    (FStar_Compiler_List.length
                                                                    d_ps))
                                                                    "params not match?" in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___29
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    Obj.magic
                                                                    uu___30 in
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_Compiler_List.zip
                                                                    d_ps a_ps in
                                                                    let subst
                                                                    =
                                                                    FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    match uu___31
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___32;
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    = uu___33;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___34;_},
                                                                    (t,
                                                                    uu___35))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps in
                                                                    let bs3 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs2 in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    match uu___31
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___32;
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    = uu___33;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___34;_},
                                                                    (t,
                                                                    uu___35))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (FStar_Pervasives_Native.Some
                                                                    t))),
                                                                    true))
                                                                    d_ps_a_ps in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    match uu___31
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = bq;
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    = uu___32;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___33;_}
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    bq))) bs3 in
                                                                    let subpats
                                                                    =
                                                                    FStar_Compiler_List.op_At
                                                                    subpats_1
                                                                    subpats_2 in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    a_us),
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
                                                                    let uu___31
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.intactics
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.intactics);
                                                                    FStar_TypeChecker_Env.nocoerce
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.nocoerce);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                                                    FStar_TypeChecker_Env.teq_nosmt_force
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                                                                    FStar_TypeChecker_Env.subtype_nosmt_force
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.erasable_types_tab);
                                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                                                                    FStar_TypeChecker_Env.unif_allow_ref_guards
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                                                    FStar_TypeChecker_Env.erase_erasable_args
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.erase_erasable_args);
                                                                    FStar_TypeChecker_Env.core_check
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.core_check)
                                                                    } s_ty1
                                                                    pat in
                                                                    match uu___31
                                                                    with
                                                                    | 
                                                                    (uu___32,
                                                                    uu___33,
                                                                    uu___34,
                                                                    uu___35,
                                                                    pat_t,
                                                                    uu___36,
                                                                    _guard_pat,
                                                                    _erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    uu___38 in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu___37 in
                                                                    let cod1
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b in
                                                                    [uu___38] in
                                                                    let uu___38
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu___37
                                                                    uu___38 in
                                                                    let nty =
                                                                    let uu___37
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu___37 in
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    FStar_Tactics_Monad.goal_typedness_deps
                                                                    g in
                                                                    FStar_Tactics_Monad.new_uvar
                                                                    "destruct branch"
                                                                    env1 nty
                                                                    FStar_Pervasives_Native.None
                                                                    uu___38
                                                                    (rangeof
                                                                    g) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___37)
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    Obj.magic
                                                                    uu___38 in
                                                                    match uu___38
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
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit in
                                                                    [uu___40] in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu___39 in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1) in
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    let uu___41
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_Compiler_List.length
                                                                    bs3) in
                                                                    (fv1,
                                                                    uu___41) in
                                                                    (g', br,
                                                                    uu___40) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___39)))
                                                                    uu___38)))
                                                                    uu___30)))
                                                                    uu___27))))))
                                                                    uu___21))
                                                                    | 
                                                                    uu___18
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Monad.fail
                                                                    "impossible: not a ctor"))))
                                                                    uu___17)
                                                                    (Obj.magic
                                                                    c_lids)) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    goal_brs
                                                                    ->
                                                                    let goal_brs
                                                                    =
                                                                    Obj.magic
                                                                    goal_brs in
                                                                    let uu___17
                                                                    =
                                                                    FStar_Compiler_List.unzip3
                                                                    goal_brs in
                                                                    match uu___17
                                                                    with
                                                                    | 
                                                                    (goals,
                                                                    brs,
                                                                    infos) ->
                                                                    let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    {
                                                                    FStar_Syntax_Syntax.scrutinee
                                                                    = s_tm1;
                                                                    FStar_Syntax_Syntax.ret_opt
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    FStar_Syntax_Syntax.brs
                                                                    = brs;
                                                                    FStar_Syntax_Syntax.rc_opt1
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })
                                                                    s_tm1.FStar_Syntax_Syntax.pos in
                                                                    let uu___18
                                                                    =
                                                                    solve' g
                                                                    w in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___18
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    Obj.magic
                                                                    uu___19 in
                                                                    FStar_Tactics_Monad.mark_goal_implicit_already_checked
                                                                    g;
                                                                    (
                                                                    let uu___21
                                                                    =
                                                                    FStar_Tactics_Monad.add_goals
                                                                    goals in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___21
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    Obj.magic
                                                                    uu___22 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    FStar_Tactics_Monad.monad_tac
                                                                    ()
                                                                    (Obj.magic
                                                                    infos)))
                                                                    uu___22))))
                                                                    uu___19)))
                                                                    uu___17)))
                                                                    uu___14)))
                                                                    uu___12))
                                                                    | 
                                                                    uu___9 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Monad.fail
                                                                    "not an inductive type")))))
                                                         uu___7))) uu___4)))
                           uu___2))) uu___1)) in
    FStar_Tactics_Monad.wrap_err "destruct" uu___
let (gather_explicit_guards_for_resolved_goals :
  unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac () (Obj.repr ())
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> FStar_Compiler_Effect.failwith "last: empty list"
    | x::[] -> x
    | uu___::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> FStar_Compiler_Effect.failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu___ = init xs in x :: uu___
let (lget :
  FStar_Syntax_Syntax.typ ->
    Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun k ->
      let uu___ =
        Obj.magic
          (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
             (Obj.magic FStar_Tactics_Monad.get)
             (fun uu___1 ->
                (fun ps ->
                   let ps = Obj.magic ps in
                   let uu___1 =
                     FStar_Compiler_Util.psmap_try_find
                       ps.FStar_Tactics_Types.local_state k in
                   match uu___1 with
                   | FStar_Pervasives_Native.None ->
                       Obj.magic (FStar_Tactics_Monad.fail "not found")
                   | FStar_Pervasives_Native.Some t ->
                       Obj.magic (unquote ty t)) uu___1)) in
      FStar_Tactics_Monad.wrap_err "lget" uu___
let (lset :
  FStar_Syntax_Syntax.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun _ty ->
    fun k ->
      fun t ->
        let uu___ =
          FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            (Obj.magic FStar_Tactics_Monad.get)
            (fun uu___1 ->
               (fun ps ->
                  let ps = Obj.magic ps in
                  let ps1 =
                    let uu___1 =
                      FStar_Compiler_Util.psmap_add
                        ps.FStar_Tactics_Types.local_state k t in
                    {
                      FStar_Tactics_Types.main_context =
                        (ps.FStar_Tactics_Types.main_context);
                      FStar_Tactics_Types.all_implicits =
                        (ps.FStar_Tactics_Types.all_implicits);
                      FStar_Tactics_Types.goals =
                        (ps.FStar_Tactics_Types.goals);
                      FStar_Tactics_Types.smt_goals =
                        (ps.FStar_Tactics_Types.smt_goals);
                      FStar_Tactics_Types.depth =
                        (ps.FStar_Tactics_Types.depth);
                      FStar_Tactics_Types.__dump =
                        (ps.FStar_Tactics_Types.__dump);
                      FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
                      FStar_Tactics_Types.entry_range =
                        (ps.FStar_Tactics_Types.entry_range);
                      FStar_Tactics_Types.guard_policy =
                        (ps.FStar_Tactics_Types.guard_policy);
                      FStar_Tactics_Types.freshness =
                        (ps.FStar_Tactics_Types.freshness);
                      FStar_Tactics_Types.tac_verb_dbg =
                        (ps.FStar_Tactics_Types.tac_verb_dbg);
                      FStar_Tactics_Types.local_state = uu___1;
                      FStar_Tactics_Types.urgency =
                        (ps.FStar_Tactics_Types.urgency)
                    } in
                  Obj.magic (FStar_Tactics_Monad.set ps1)) uu___1) in
        FStar_Tactics_Monad.wrap_err "lset" uu___
let (set_urgency : FStar_BigInt.t -> unit FStar_Tactics_Monad.tac) =
  fun u ->
    FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
      (Obj.magic FStar_Tactics_Monad.get)
      (fun uu___ ->
         (fun ps ->
            let ps = Obj.magic ps in
            let ps1 =
              let uu___ = FStar_BigInt.to_int_fs u in
              {
                FStar_Tactics_Types.main_context =
                  (ps.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.all_implicits =
                  (ps.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (ps.FStar_Tactics_Types.goals);
                FStar_Tactics_Types.smt_goals =
                  (ps.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (ps.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (ps.FStar_Tactics_Types.guard_policy);
                FStar_Tactics_Types.freshness =
                  (ps.FStar_Tactics_Types.freshness);
                FStar_Tactics_Types.tac_verb_dbg =
                  (ps.FStar_Tactics_Types.tac_verb_dbg);
                FStar_Tactics_Types.local_state =
                  (ps.FStar_Tactics_Types.local_state);
                FStar_Tactics_Types.urgency = uu___
              } in
            Obj.magic (FStar_Tactics_Monad.set ps1)) uu___)
let (t_commute_applied_match : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
        (Obj.magic FStar_Tactics_Monad.cur_goal)
        (fun uu___2 ->
           (fun g ->
              let g = Obj.magic g in
              let uu___2 =
                let uu___3 = FStar_Tactics_Types.goal_env g in
                let uu___4 = FStar_Tactics_Types.goal_type g in
                destruct_eq uu___3 uu___4 in
              match uu___2 with
              | FStar_Pervasives_Native.Some (l, r) ->
                  let uu___3 = FStar_Syntax_Util.head_and_args_full l in
                  (match uu___3 with
                   | (lh, las) ->
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = FStar_Syntax_Util.unascribe lh in
                           FStar_Syntax_Subst.compress uu___6 in
                         uu___5.FStar_Syntax_Syntax.n in
                       (match uu___4 with
                        | FStar_Syntax_Syntax.Tm_match
                            { FStar_Syntax_Syntax.scrutinee = e;
                              FStar_Syntax_Syntax.ret_opt = asc_opt;
                              FStar_Syntax_Syntax.brs = brs;
                              FStar_Syntax_Syntax.rc_opt1 = lopt;_}
                            ->
                            let brs' =
                              FStar_Compiler_List.map
                                (fun uu___5 ->
                                   match uu___5 with
                                   | (p, w, e1) ->
                                       let uu___6 =
                                         FStar_Syntax_Util.mk_app e1 las in
                                       (p, w, uu___6)) brs in
                            let lopt' =
                              FStar_Compiler_Util.map_option
                                (fun rc ->
                                   let uu___5 =
                                     FStar_Compiler_Util.map_option
                                       (fun t ->
                                          let uu___6 =
                                            let uu___7 =
                                              FStar_Tactics_Types.goal_env g in
                                            FStar_TypeChecker_Normalize.get_n_binders
                                              uu___7
                                              (FStar_Compiler_List.length las)
                                              t in
                                          match uu___6 with
                                          | (bs, c) ->
                                              let uu___7 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs c in
                                              (match uu___7 with
                                               | (bs1, c1) ->
                                                   let ss =
                                                     FStar_Compiler_List.map2
                                                       (fun b ->
                                                          fun a ->
                                                            FStar_Syntax_Syntax.NT
                                                              ((b.FStar_Syntax_Syntax.binder_bv),
                                                                (FStar_Pervasives_Native.fst
                                                                   a))) bs1
                                                       las in
                                                   let c2 =
                                                     FStar_Syntax_Subst.subst_comp
                                                       ss c1 in
                                                   FStar_Syntax_Util.comp_result
                                                     c2))
                                       rc.FStar_Syntax_Syntax.residual_typ in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (rc.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu___5;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (rc.FStar_Syntax_Syntax.residual_flags)
                                   }) lopt in
                            let l' =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   {
                                     FStar_Syntax_Syntax.scrutinee = e;
                                     FStar_Syntax_Syntax.ret_opt = asc_opt;
                                     FStar_Syntax_Syntax.brs = brs';
                                     FStar_Syntax_Syntax.rc_opt1 = lopt'
                                   }) l.FStar_Syntax_Syntax.pos in
                            let must_tot = true in
                            let uu___5 =
                              let uu___6 = FStar_Tactics_Types.goal_env g in
                              do_unify_maybe_guards false must_tot uu___6 l'
                                r in
                            Obj.magic
                              (FStar_Class_Monad.op_let_Bang
                                 FStar_Tactics_Monad.monad_tac () ()
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    (fun uu___6 ->
                                       let uu___6 = Obj.magic uu___6 in
                                       match uu___6 with
                                       | FStar_Pervasives_Native.None ->
                                           Obj.magic
                                             (FStar_Tactics_Monad.fail
                                                "discharging the equality failed")
                                       | FStar_Pervasives_Native.Some guard
                                           ->
                                           let uu___7 =
                                             FStar_TypeChecker_Env.is_trivial_guard_formula
                                               guard in
                                           if uu___7
                                           then
                                             (FStar_Tactics_Monad.mark_uvar_as_already_checked
                                                g.FStar_Tactics_Types.goal_ctx_uvar;
                                              Obj.magic
                                                (solve g
                                                   FStar_Syntax_Util.exp_unit))
                                           else
                                             Obj.magic
                                               (FStar_Compiler_Effect.failwith
                                                  "internal error: _t_refl: guard is not trivial"))
                                      uu___6))
                        | uu___5 ->
                            Obj.magic
                              (FStar_Tactics_Monad.fail "lhs is not a match")))
              | FStar_Pervasives_Native.None ->
                  Obj.magic (FStar_Tactics_Monad.fail "not an equality"))
             uu___2) in
    FStar_Tactics_Monad.wrap_err "t_commute_applied_match" uu___1
let (string_to_term :
  env -> Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac) =
  fun e ->
    fun s ->
      let frag_of_text s1 =
        {
          FStar_Parser_ParseIt.frag_fname = "<string_of_term>";
          FStar_Parser_ParseIt.frag_text = s1;
          FStar_Parser_ParseIt.frag_line = Prims.int_one;
          FStar_Parser_ParseIt.frag_col = Prims.int_zero
        } in
      let uu___ =
        FStar_Parser_ParseIt.parse
          (FStar_Parser_ParseIt.Fragment (frag_of_text s)) in
      match uu___ with
      | FStar_Parser_ParseIt.Term t ->
          let dsenv =
            let uu___1 = FStar_TypeChecker_Env.current_module e in
            FStar_Syntax_DsEnv.set_current_module
              e.FStar_TypeChecker_Env.dsenv uu___1 in
          (try
             (fun uu___1 ->
                (fun uu___1 ->
                   match () with
                   | () ->
                       let uu___2 =
                         FStar_ToSyntax_ToSyntax.desugar_term dsenv t in
                       Obj.magic
                         (FStar_Class_Monad.return
                            FStar_Tactics_Monad.monad_tac ()
                            (Obj.magic uu___2))) uu___1) ()
           with
           | FStar_Errors.Error (uu___2, e1, uu___3, uu___4) ->
               let uu___5 =
                 let uu___6 = FStar_Errors_Msg.rendermsg e1 in
                 Prims.strcat "string_to_term: " uu___6 in
               FStar_Tactics_Monad.fail uu___5
           | uu___2 ->
               FStar_Tactics_Monad.fail "string_to_term: Unknown error")
      | FStar_Parser_ParseIt.ASTFragment uu___1 ->
          FStar_Tactics_Monad.fail
            "string_to_term: expected a Term as a result, got an ASTFragment"
      | FStar_Parser_ParseIt.ParseError (uu___1, err, uu___2) ->
          let uu___3 =
            let uu___4 = FStar_Errors_Msg.rendermsg err in
            Prims.strcat "string_to_term: got error " uu___4 in
          FStar_Tactics_Monad.fail uu___3
let (push_bv_dsenv :
  env ->
    Prims.string ->
      (env * FStar_Reflection_V2_Data.binding) FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun e ->
         fun i ->
           let ident =
             FStar_Ident.mk_ident (i, FStar_Compiler_Range_Type.dummyRange) in
           let uu___ =
             FStar_Syntax_DsEnv.push_bv e.FStar_TypeChecker_Env.dsenv ident in
           match uu___ with
           | (dsenv, bv) ->
               let uu___1 =
                 let uu___2 = bv_to_binding bv in
                 ({
                    FStar_TypeChecker_Env.solver =
                      (e.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (e.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (e.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (e.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (e.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (e.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (e.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (e.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (e.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (e.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (e.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (e.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (e.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (e.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (e.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (e.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (e.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (e.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (e.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = (e.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (e.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (e.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (e.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (e.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (e.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.intactics =
                      (e.FStar_TypeChecker_Env.intactics);
                    FStar_TypeChecker_Env.nocoerce =
                      (e.FStar_TypeChecker_Env.nocoerce);
                    FStar_TypeChecker_Env.tc_term =
                      (e.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                      (e.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                    FStar_TypeChecker_Env.universe_of =
                      (e.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                      =
                      (e.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                    FStar_TypeChecker_Env.teq_nosmt_force =
                      (e.FStar_TypeChecker_Env.teq_nosmt_force);
                    FStar_TypeChecker_Env.subtype_nosmt_force =
                      (e.FStar_TypeChecker_Env.subtype_nosmt_force);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (e.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (e.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (e.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (e.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (e.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (e.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (e.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (e.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (e.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (e.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (e.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv = dsenv;
                    FStar_TypeChecker_Env.nbe = (e.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (e.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (e.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (e.FStar_TypeChecker_Env.enable_defer_to_tac);
                    FStar_TypeChecker_Env.unif_allow_ref_guards =
                      (e.FStar_TypeChecker_Env.unif_allow_ref_guards);
                    FStar_TypeChecker_Env.erase_erasable_args =
                      (e.FStar_TypeChecker_Env.erase_erasable_args);
                    FStar_TypeChecker_Env.core_check =
                      (e.FStar_TypeChecker_Env.core_check)
                  }, uu___2) in
               Obj.magic
                 (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                    (Obj.magic uu___1))) uu___1 uu___
let (term_to_string :
  FStar_Syntax_Syntax.term -> Prims.string FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun t ->
       let uu___ = top_env () in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun g ->
                  let g = Obj.magic g in
                  let s =
                    FStar_Syntax_Print.term_to_string'
                      g.FStar_TypeChecker_Env.dsenv t in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic s))) uu___1))) uu___
let (comp_to_string :
  FStar_Syntax_Syntax.comp -> Prims.string FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun c ->
       let uu___ = top_env () in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun g ->
                  let g = Obj.magic g in
                  let s =
                    FStar_Syntax_Print.comp_to_string'
                      g.FStar_TypeChecker_Env.dsenv c in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic s))) uu___1))) uu___
let (term_to_doc :
  FStar_Syntax_Syntax.term -> FStar_Pprint.document FStar_Tactics_Monad.tac)
  =
  fun uu___ ->
    (fun t ->
       let uu___ = top_env () in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun g ->
                  let g = Obj.magic g in
                  let s =
                    FStar_Syntax_Print.term_to_doc'
                      g.FStar_TypeChecker_Env.dsenv t in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic s))) uu___1))) uu___
let (comp_to_doc :
  FStar_Syntax_Syntax.comp -> FStar_Pprint.document FStar_Tactics_Monad.tac)
  =
  fun uu___ ->
    (fun c ->
       let uu___ = top_env () in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun g ->
                  let g = Obj.magic g in
                  let s =
                    FStar_Syntax_Print.comp_to_doc'
                      g.FStar_TypeChecker_Env.dsenv c in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic s))) uu___1))) uu___
let (range_to_string :
  FStar_Compiler_Range_Type.range -> Prims.string FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun r ->
       let uu___ =
         FStar_Class_Show.show FStar_Compiler_Range_Ops.show_range r in
       Obj.magic
         (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
            (Obj.magic uu___))) uu___
let (term_eq_old :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t1 ->
         fun t2 ->
           let uu___ =
             FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
               (Obj.repr ()) in
           Obj.magic
             (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                () uu___
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in
                      let uu___2 = FStar_Syntax_Util.term_eq t1 t2 in
                      Obj.magic
                        (FStar_Class_Monad.return
                           FStar_Tactics_Monad.monad_tac ()
                           (Obj.magic uu___2))) uu___1))) uu___1 uu___
let with_compat_pre_core :
  'a .
    FStar_BigInt.t ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun n ->
    fun f ->
      FStar_Tactics_Monad.mk_tac
        (fun ps ->
           FStar_Options.with_saved_options
             (fun uu___ ->
                let _res = FStar_Options.set_options "--compat_pre_core 0" in
                FStar_Tactics_Monad.run f ps))
let (get_vconfig : unit -> FStar_VConfig.vconfig FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            (Obj.magic FStar_Tactics_Monad.cur_goal)
            (fun uu___1 ->
               (fun g ->
                  let g = Obj.magic g in
                  let vcfg =
                    FStar_Options.with_saved_options
                      (fun uu___1 ->
                         (let uu___3 =
                            FStar_Compiler_Util.smap_copy
                              g.FStar_Tactics_Types.opts in
                          FStar_Options.set uu___3);
                         FStar_Options.get_vconfig ()) in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic vcfg))) uu___1))) uu___
let (set_vconfig : FStar_VConfig.vconfig -> unit FStar_Tactics_Monad.tac) =
  fun vcfg ->
    FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
      (Obj.magic FStar_Tactics_Monad.cur_goal)
      (fun uu___ ->
         (fun g ->
            let g = Obj.magic g in
            let opts' =
              FStar_Options.with_saved_options
                (fun uu___ ->
                   (let uu___2 =
                      FStar_Compiler_Util.smap_copy
                        g.FStar_Tactics_Types.opts in
                    FStar_Options.set uu___2);
                   FStar_Options.set_vconfig vcfg;
                   FStar_Options.peek ()) in
            let g' =
              {
                FStar_Tactics_Types.goal_main_env =
                  (g.FStar_Tactics_Types.goal_main_env);
                FStar_Tactics_Types.goal_ctx_uvar =
                  (g.FStar_Tactics_Types.goal_ctx_uvar);
                FStar_Tactics_Types.opts = opts';
                FStar_Tactics_Types.is_guard =
                  (g.FStar_Tactics_Types.is_guard);
                FStar_Tactics_Types.label = (g.FStar_Tactics_Types.label)
              } in
            Obj.magic (FStar_Tactics_Monad.replace_cur g')) uu___)
let (t_smt_sync : FStar_VConfig.vconfig -> unit FStar_Tactics_Monad.tac) =
  fun vcfg ->
    let uu___ =
      FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
        (Obj.magic FStar_Tactics_Monad.cur_goal)
        (fun uu___1 ->
           (fun goal ->
              let goal = Obj.magic goal in
              let uu___1 = FStar_Tactics_Monad.get_phi goal in
              match uu___1 with
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (FStar_Tactics_Monad.fail "Goal is not irrelevant")
              | FStar_Pervasives_Native.Some phi ->
                  let e = FStar_Tactics_Types.goal_env goal in
                  let ans =
                    FStar_Options.with_saved_options
                      (fun uu___2 ->
                         FStar_Options.set_vconfig vcfg;
                         (e.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve_sync
                           FStar_Pervasives_Native.None e phi) in
                  if ans
                  then
                    (FStar_Tactics_Monad.mark_uvar_as_already_checked
                       goal.FStar_Tactics_Types.goal_ctx_uvar;
                     Obj.magic (solve goal FStar_Syntax_Util.exp_unit))
                  else
                    Obj.magic
                      (FStar_Tactics_Monad.fail "SMT did not solve this goal"))
             uu___1) in
    FStar_Tactics_Monad.wrap_err "t_smt_sync" uu___
let (free_uvars :
  FStar_Syntax_Syntax.term ->
    FStar_BigInt.t Prims.list FStar_Tactics_Monad.tac)
  =
  fun uu___ ->
    (fun tm ->
       let uu___ =
         FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
           (Obj.repr ()) in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            uu___
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___1 = Obj.magic uu___1 in
                  let uvs =
                    let uu___2 =
                      let uu___3 = FStar_Syntax_Free.uvars_uncached tm in
                      FStar_Compiler_Set.elems FStar_Syntax_Free.ord_ctx_uvar
                        uu___3 in
                    FStar_Compiler_List.map
                      (fun u ->
                         let uu___3 =
                           FStar_Syntax_Unionfind.uvar_id
                             u.FStar_Syntax_Syntax.ctx_uvar_head in
                         FStar_BigInt.of_int_fs uu___3) uu___2 in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic uvs))) uu___1))) uu___
let (all_ext_options :
  unit -> (Prims.string * Prims.string) Prims.list FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun uu___ ->
       let uu___1 =
         FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
           (Obj.repr ()) in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            uu___1
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___2 = Obj.magic uu___2 in
                  let uu___3 = FStar_Options.all_ext_options () in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic uu___3))) uu___2))) uu___
let (ext_getv : Prims.string -> Prims.string FStar_Tactics_Monad.tac) =
  fun uu___ ->
    (fun k ->
       let uu___ =
         FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
           (Obj.repr ()) in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            uu___
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___1 = Obj.magic uu___1 in
                  let uu___2 = FStar_Options.ext_getv k in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic uu___2))) uu___1))) uu___
let (ext_getns :
  Prims.string ->
    (Prims.string * Prims.string) Prims.list FStar_Tactics_Monad.tac)
  =
  fun uu___ ->
    (fun ns ->
       let uu___ =
         FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
           (Obj.repr ()) in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            uu___
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___1 = Obj.magic uu___1 in
                  let uu___2 = FStar_Options.ext_getns ns in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic uu___2))) uu___1))) uu___
let alloc : 'a . 'a -> 'a FStar_Tactics_Types.tref FStar_Tactics_Monad.tac =
  fun uu___ ->
    (fun x ->
       let uu___ =
         FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
           (Obj.repr ()) in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            uu___
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___1 = Obj.magic uu___1 in
                  let uu___2 = FStar_Compiler_Util.mk_ref x in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic uu___2))) uu___1))) uu___
let read : 'a . 'a FStar_Tactics_Types.tref -> 'a FStar_Tactics_Monad.tac =
  fun uu___ ->
    (fun r ->
       let uu___ =
         FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
           (Obj.repr ()) in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
            uu___
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___1 = Obj.magic uu___1 in
                  let uu___2 = FStar_Compiler_Effect.op_Bang r in
                  Obj.magic
                    (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.magic uu___2))) uu___1))) uu___
let write :
  'a . 'a FStar_Tactics_Types.tref -> 'a -> unit FStar_Tactics_Monad.tac =
  fun r ->
    fun x ->
      let uu___ =
        FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
          (Obj.repr ()) in
      FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () () uu___
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___1 = Obj.magic uu___1 in
              FStar_Compiler_Effect.op_Colon_Equals r x;
              Obj.magic
                (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                   (Obj.repr ()))) uu___1)
let (dbg_refl : env -> (unit -> Prims.string) -> unit) =
  fun g ->
    fun msg ->
      let uu___ =
        FStar_TypeChecker_Env.debug g (FStar_Options.Other "ReflTc") in
      if uu___
      then let uu___1 = msg () in FStar_Compiler_Util.print_string uu___1
      else ()
type issues = FStar_Errors.issue Prims.list
let (refl_typing_guard :
  env -> FStar_Syntax_Syntax.typ -> unit FStar_Tactics_Monad.tac) =
  fun e ->
    fun g ->
      let reason = "refl_typing_guard" in
      let uu___ = FStar_TypeChecker_Env.get_range e in
      proc_guard_formula "refl_typing_guard" e g FStar_Pervasives_Native.None
        uu___
let uncurry :
  'uuuuu 'uuuuu1 'uuuuu2 .
    ('uuuuu -> 'uuuuu1 -> 'uuuuu2) -> ('uuuuu * 'uuuuu1) -> 'uuuuu2
  = fun f -> fun uu___ -> match uu___ with | (x, y) -> f x y
let __refl_typing_builtin_wrapper :
  'a .
    (unit -> ('a * (env * FStar_Syntax_Syntax.typ) Prims.list)) ->
      ('a FStar_Pervasives_Native.option * issues) FStar_Tactics_Monad.tac
  =
  fun uu___ ->
    (fun f ->
       let tx = FStar_Syntax_Unionfind.new_transaction () in
       let uu___ =
         try
           (fun uu___1 ->
              match () with
              | () -> FStar_Errors.catch_errors_and_ignore_rest f) ()
         with
         | uu___1 ->
             let issue =
               let uu___2 =
                 let uu___3 = FStar_Compiler_Util.print_exn uu___1 in
                 FStar_Errors_Msg.mkmsg uu___3 in
               let uu___3 = FStar_Errors.get_ctx () in
               {
                 FStar_Errors.issue_msg = uu___2;
                 FStar_Errors.issue_level = FStar_Errors.EError;
                 FStar_Errors.issue_range = FStar_Pervasives_Native.None;
                 FStar_Errors.issue_number =
                   (FStar_Pervasives_Native.Some (Prims.of_int (17)));
                 FStar_Errors.issue_ctx = uu___3
               } in
             ([issue], FStar_Pervasives_Native.None) in
       match uu___ with
       | (errs, r) ->
           let gs =
             if FStar_Pervasives_Native.uu___is_Some r
             then
               let allow_uvars = false in
               let allow_names = true in
               FStar_Compiler_List.map
                 (fun uu___1 ->
                    match uu___1 with
                    | (e, g) ->
                        let uu___2 =
                          FStar_Syntax_Compress.deep_compress allow_uvars
                            allow_names g in
                        (e, uu___2))
                 (FStar_Pervasives_Native.snd
                    (FStar_Pervasives_Native.__proj__Some__item__v r))
             else [] in
           let r1 = FStar_Compiler_Util.map_opt r FStar_Pervasives_Native.fst in
           Obj.magic
             (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                () (Obj.magic FStar_Tactics_Monad.get)
                (fun uu___1 ->
                   (fun ps ->
                      let ps = Obj.magic ps in
                      FStar_TypeChecker_Env.promote_id_info
                        ps.FStar_Tactics_Types.main_context
                        (FStar_TypeChecker_Tc.compress_and_norm
                           ps.FStar_Tactics_Types.main_context);
                      FStar_Syntax_Unionfind.rollback tx;
                      if (FStar_Compiler_List.length errs) > Prims.int_zero
                      then
                        Obj.magic
                          (FStar_Class_Monad.return
                             FStar_Tactics_Monad.monad_tac ()
                             (Obj.magic (FStar_Pervasives_Native.None, errs)))
                      else
                        (let uu___4 =
                           FStar_Tactics_Monad.iter_tac
                             (uncurry refl_typing_guard) gs in
                         Obj.magic
                           (FStar_Class_Monad.op_let_Bang
                              FStar_Tactics_Monad.monad_tac () () uu___4
                              (fun uu___5 ->
                                 (fun uu___5 ->
                                    let uu___5 = Obj.magic uu___5 in
                                    Obj.magic
                                      (FStar_Class_Monad.return
                                         FStar_Tactics_Monad.monad_tac ()
                                         (Obj.magic (r1, errs)))) uu___5))))
                     uu___1))) uu___
let catch_all :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (issues, 'a) FStar_Pervasives.either FStar_Tactics_Monad.tac
  =
  fun f ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let uu___ =
           FStar_Errors.catch_errors_and_ignore_rest
             (fun uu___1 -> FStar_Tactics_Monad.run f ps) in
         match uu___ with
         | ([], FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
            (v, ps'))) ->
             FStar_Tactics_Result.Success ((FStar_Pervasives.Inr v), ps')
         | (errs, uu___1) ->
             FStar_Tactics_Result.Success ((FStar_Pervasives.Inl errs), ps))
let refl_typing_builtin_wrapper :
  'a .
    Prims.string ->
      (unit -> ('a * (env * FStar_Syntax_Syntax.typ) Prims.list)) ->
        ('a FStar_Pervasives_Native.option * issues) FStar_Tactics_Monad.tac
  =
  fun uu___1 ->
    fun uu___ ->
      (fun label ->
         fun f ->
           let uu___ =
             let uu___1 =
               let uu___2 = __refl_typing_builtin_wrapper f in
               catch_all uu___2 in
             Obj.magic
               (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac
                  () () (Obj.magic uu___1)
                  (fun uu___2 ->
                     (fun uu___2 ->
                        let uu___2 = Obj.magic uu___2 in
                        match uu___2 with
                        | FStar_Pervasives.Inl errs ->
                            Obj.magic
                              (FStar_Class_Monad.return
                                 FStar_Tactics_Monad.monad_tac ()
                                 (Obj.magic
                                    (FStar_Pervasives_Native.None, errs)))
                        | FStar_Pervasives.Inr r ->
                            Obj.magic
                              (FStar_Class_Monad.return
                                 FStar_Tactics_Monad.monad_tac ()
                                 (Obj.magic r))) uu___2)) in
           Obj.magic
             (FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac ()
                () (Obj.magic uu___)
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in
                      match uu___1 with
                      | (o, errs) ->
                          let errs1 =
                            FStar_Compiler_List.map
                              (fun is ->
                                 let uu___2 =
                                   let uu___3 =
                                     let uu___4 =
                                       FStar_Errors_Msg.text
                                         (Prims.strcat
                                            "Raised within Tactics." label) in
                                     [uu___4] in
                                   FStar_Compiler_List.op_At
                                     is.FStar_Errors.issue_msg uu___3 in
                                 {
                                   FStar_Errors.issue_msg = uu___2;
                                   FStar_Errors.issue_level =
                                     (is.FStar_Errors.issue_level);
                                   FStar_Errors.issue_range =
                                     (is.FStar_Errors.issue_range);
                                   FStar_Errors.issue_number =
                                     (is.FStar_Errors.issue_number);
                                   FStar_Errors.issue_ctx =
                                     (is.FStar_Errors.issue_ctx)
                                 }) errs in
                          Obj.magic
                            (FStar_Class_Monad.return
                               FStar_Tactics_Monad.monad_tac ()
                               (Obj.magic (o, errs1)))) uu___1))) uu___1
        uu___
let (no_uvars_in_term : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    (let uu___ = FStar_Syntax_Free.uvars t in
     FStar_Compiler_Set.is_empty FStar_Syntax_Free.ord_ctx_uvar uu___) &&
      (let uu___ = FStar_Syntax_Free.univs t in
       FStar_Compiler_Set.is_empty FStar_Syntax_Free.ord_univ_uvar uu___)
let (no_univ_uvars_in_term : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = FStar_Syntax_Free.univs t in
    FStar_Compiler_Set.is_empty FStar_Syntax_Free.ord_univ_uvar uu___
let (no_uvars_in_g : env -> Prims.bool) =
  fun g ->
    FStar_Compiler_Util.for_all
      (fun uu___ ->
         match uu___ with
         | FStar_Syntax_Syntax.Binding_var bv ->
             no_uvars_in_term bv.FStar_Syntax_Syntax.sort
         | uu___1 -> true) g.FStar_TypeChecker_Env.gamma
type relation =
  | Subtyping 
  | Equality 
let (uu___is_Subtyping : relation -> Prims.bool) =
  fun projectee -> match projectee with | Subtyping -> true | uu___ -> false
let (uu___is_Equality : relation -> Prims.bool) =
  fun projectee -> match projectee with | Equality -> true | uu___ -> false
let (unexpected_uvars_issue :
  FStar_Compiler_Range_Type.range -> FStar_Errors.issue) =
  fun r ->
    let i =
      let uu___ = FStar_Errors_Msg.mkmsg "Cannot check relation with uvars" in
      let uu___1 =
        let uu___2 =
          FStar_Errors.errno
            FStar_Errors_Codes.Error_UnexpectedUnresolvedUvar in
        FStar_Pervasives_Native.Some uu___2 in
      {
        FStar_Errors.issue_msg = uu___;
        FStar_Errors.issue_level = FStar_Errors.EError;
        FStar_Errors.issue_range = (FStar_Pervasives_Native.Some r);
        FStar_Errors.issue_number = uu___1;
        FStar_Errors.issue_ctx = []
      } in
    i
let (refl_is_non_informative :
  env ->
    FStar_Syntax_Syntax.typ ->
      (unit FStar_Pervasives_Native.option * issues) FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           let uu___ = (no_uvars_in_g g) && (no_uvars_in_term t) in
           if uu___
           then
             Obj.magic
               (Obj.repr
                  (refl_typing_builtin_wrapper "refl_is_non_informative"
                     (fun uu___1 ->
                        let g1 =
                          FStar_TypeChecker_Env.set_range g
                            t.FStar_Syntax_Syntax.pos in
                        dbg_refl g1
                          (fun uu___3 ->
                             let uu___4 =
                               FStar_Class_Show.show
                                 FStar_Syntax_Print.showable_term t in
                             FStar_Compiler_Util.format1
                               "refl_is_non_informative: %s\n" uu___4);
                        (let b =
                           FStar_TypeChecker_Core.is_non_informative g1 t in
                         dbg_refl g1
                           (fun uu___4 ->
                              let uu___5 =
                                FStar_Class_Show.show
                                  (FStar_Class_Show.printableshow
                                     FStar_Class_Printable.printable_bool) b in
                              FStar_Compiler_Util.format1
                                "refl_is_non_informative: returned %s" uu___5);
                         if b
                         then ((), [])
                         else
                           (let uu___5 = FStar_TypeChecker_Env.get_range g1 in
                            FStar_Errors.raise_error
                              (FStar_Errors_Codes.Fatal_UnexpectedTerm,
                                "is_non_informative returned false ") uu___5)))))
           else
             Obj.magic
               (Obj.repr
                  (let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 = FStar_TypeChecker_Env.get_range g in
                         unexpected_uvars_issue uu___5 in
                       [uu___4] in
                     (FStar_Pervasives_Native.None, uu___3) in
                   FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                     (Obj.magic uu___2)))) uu___1 uu___
let (refl_check_relation :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        relation ->
          (unit FStar_Pervasives_Native.option * issues)
            FStar_Tactics_Monad.tac)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun t0 ->
               fun t1 ->
                 fun rel ->
                   let uu___ =
                     ((no_uvars_in_g g) && (no_uvars_in_term t0)) &&
                       (no_uvars_in_term t1) in
                   if uu___
                   then
                     Obj.magic
                       (Obj.repr
                          (refl_typing_builtin_wrapper "refl_check_relation"
                             (fun uu___1 ->
                                let g1 =
                                  FStar_TypeChecker_Env.set_range g
                                    t0.FStar_Syntax_Syntax.pos in
                                dbg_refl g1
                                  (fun uu___3 ->
                                     let uu___4 =
                                       FStar_Class_Show.show
                                         FStar_Syntax_Print.showable_term t0 in
                                     let uu___5 =
                                       FStar_Class_Show.show
                                         FStar_Syntax_Print.showable_term t1 in
                                     FStar_Compiler_Util.format3
                                       "refl_check_relation: %s %s %s\n"
                                       uu___4
                                       (if rel = Subtyping
                                        then "<:?"
                                        else "=?=") uu___5);
                                (let f =
                                   if rel = Subtyping
                                   then
                                     FStar_TypeChecker_Core.check_term_subtyping
                                   else
                                     FStar_TypeChecker_Core.check_term_equality in
                                 let uu___3 = f g1 t0 t1 in
                                 match uu___3 with
                                 | FStar_Pervasives.Inl
                                     (FStar_Pervasives_Native.None) ->
                                     (dbg_refl g1
                                        (fun uu___5 ->
                                           "refl_check_relation: succeeded (no guard)");
                                      ((), []))
                                 | FStar_Pervasives.Inl
                                     (FStar_Pervasives_Native.Some guard_f)
                                     ->
                                     (dbg_refl g1
                                        (fun uu___5 ->
                                           "refl_check_relation: succeeded");
                                      ((), [(g1, guard_f)]))
                                 | FStar_Pervasives.Inr err ->
                                     (dbg_refl g1
                                        (fun uu___5 ->
                                           let uu___6 =
                                             FStar_TypeChecker_Core.print_error
                                               err in
                                           FStar_Compiler_Util.format1
                                             "refl_check_relation failed: %s\n"
                                             uu___6);
                                      (let uu___5 =
                                         let uu___6 =
                                           let uu___7 =
                                             FStar_TypeChecker_Core.print_error
                                               err in
                                           Prims.strcat
                                             "check_relation failed: " uu___7 in
                                         (FStar_Errors_Codes.Fatal_IllTyped,
                                           uu___6) in
                                       let uu___6 =
                                         FStar_TypeChecker_Env.get_range g1 in
                                       FStar_Errors.raise_error uu___5 uu___6))))))
                   else
                     Obj.magic
                       (Obj.repr
                          (let uu___2 =
                             let uu___3 =
                               let uu___4 =
                                 let uu___5 =
                                   FStar_TypeChecker_Env.get_range g in
                                 unexpected_uvars_issue uu___5 in
                               [uu___4] in
                             (FStar_Pervasives_Native.None, uu___3) in
                           FStar_Class_Monad.return
                             FStar_Tactics_Monad.monad_tac ()
                             (Obj.magic uu___2)))) uu___3 uu___2 uu___1 uu___
let (refl_check_subtyping :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        (unit FStar_Pervasives_Native.option * issues)
          FStar_Tactics_Monad.tac)
  = fun g -> fun t0 -> fun t1 -> refl_check_relation g t0 t1 Subtyping
let (refl_check_equiv :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        (unit FStar_Pervasives_Native.option * issues)
          FStar_Tactics_Monad.tac)
  = fun g -> fun t0 -> fun t1 -> refl_check_relation g t0 t1 Equality
let (to_must_tot : FStar_TypeChecker_Core.tot_or_ghost -> Prims.bool) =
  fun eff ->
    match eff with
    | FStar_TypeChecker_Core.E_Total -> true
    | FStar_TypeChecker_Core.E_Ghost -> false
let (tot_or_ghost_to_string :
  FStar_TypeChecker_Core.tot_or_ghost -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Core.E_Total -> "E_Total"
    | FStar_TypeChecker_Core.E_Ghost -> "E_Ghost"
let (refl_norm_type :
  env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun g ->
    fun t ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Env.Beta;
        FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta] g t
let (refl_core_compute_term_type :
  env ->
    FStar_Syntax_Syntax.term ->
      ((FStar_TypeChecker_Core.tot_or_ghost * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option * issues) FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun e ->
           let uu___ = (no_uvars_in_g g) && (no_uvars_in_term e) in
           if uu___
           then
             Obj.magic
               (Obj.repr
                  (refl_typing_builtin_wrapper "refl_core_compute_term_type"
                     (fun uu___1 ->
                        let g1 =
                          FStar_TypeChecker_Env.set_range g
                            e.FStar_Syntax_Syntax.pos in
                        dbg_refl g1
                          (fun uu___3 ->
                             let uu___4 =
                               FStar_Class_Show.show
                                 FStar_Syntax_Print.showable_term e in
                             FStar_Compiler_Util.format1
                               "refl_core_compute_term_type: %s\n" uu___4);
                        (let guards = FStar_Compiler_Util.mk_ref [] in
                         let gh g2 guard =
                           (let uu___4 =
                              let uu___5 =
                                FStar_Compiler_Effect.op_Bang guards in
                              (g2, guard) :: uu___5 in
                            FStar_Compiler_Effect.op_Colon_Equals guards
                              uu___4);
                           true in
                         let uu___3 =
                           FStar_TypeChecker_Core.compute_term_type_handle_guards
                             g1 e gh in
                         match uu___3 with
                         | FStar_Pervasives.Inl (eff, t) ->
                             let t1 = refl_norm_type g1 t in
                             (dbg_refl g1
                                (fun uu___5 ->
                                   let uu___6 =
                                     FStar_Class_Show.show
                                       FStar_Syntax_Print.showable_term e in
                                   let uu___7 =
                                     FStar_Class_Show.show
                                       FStar_Syntax_Print.showable_term t1 in
                                   FStar_Compiler_Util.format2
                                     "refl_core_compute_term_type for %s computed type %s\n"
                                     uu___6 uu___7);
                              (let uu___5 =
                                 FStar_Compiler_Effect.op_Bang guards in
                               ((eff, t1), uu___5)))
                         | FStar_Pervasives.Inr err ->
                             (dbg_refl g1
                                (fun uu___5 ->
                                   let uu___6 =
                                     FStar_TypeChecker_Core.print_error err in
                                   FStar_Compiler_Util.format1
                                     "refl_core_compute_term_type: %s\n"
                                     uu___6);
                              (let uu___5 =
                                 let uu___6 =
                                   let uu___7 =
                                     FStar_TypeChecker_Core.print_error err in
                                   Prims.strcat
                                     "core_compute_term_type failed: " uu___7 in
                                 (FStar_Errors_Codes.Fatal_IllTyped, uu___6) in
                               let uu___6 =
                                 FStar_TypeChecker_Env.get_range g1 in
                               FStar_Errors.raise_error uu___5 uu___6))))))
           else
             Obj.magic
               (Obj.repr
                  (let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 = FStar_TypeChecker_Env.get_range g in
                         unexpected_uvars_issue uu___5 in
                       [uu___4] in
                     (FStar_Pervasives_Native.None, uu___3) in
                   FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                     (Obj.magic uu___2)))) uu___1 uu___
let (refl_core_check_term :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Core.tot_or_ghost ->
          (unit FStar_Pervasives_Native.option * issues)
            FStar_Tactics_Monad.tac)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun e ->
               fun t ->
                 fun eff ->
                   let uu___ =
                     ((no_uvars_in_g g) && (no_uvars_in_term e)) &&
                       (no_uvars_in_term t) in
                   if uu___
                   then
                     Obj.magic
                       (Obj.repr
                          (refl_typing_builtin_wrapper "refl_core_check_term"
                             (fun uu___1 ->
                                let g1 =
                                  FStar_TypeChecker_Env.set_range g
                                    e.FStar_Syntax_Syntax.pos in
                                dbg_refl g1
                                  (fun uu___3 ->
                                     let uu___4 =
                                       FStar_Class_Show.show
                                         FStar_Syntax_Print.showable_term e in
                                     let uu___5 =
                                       FStar_Class_Show.show
                                         FStar_Syntax_Print.showable_term t in
                                     FStar_Compiler_Util.format3
                                       "refl_core_check_term: term: %s, type: %s, eff: %s\n"
                                       uu___4 uu___5
                                       (tot_or_ghost_to_string eff));
                                (let must_tot = to_must_tot eff in
                                 let uu___3 =
                                   FStar_TypeChecker_Core.check_term g1 e t
                                     must_tot in
                                 match uu___3 with
                                 | FStar_Pervasives.Inl
                                     (FStar_Pervasives_Native.None) ->
                                     (dbg_refl g1
                                        (fun uu___5 ->
                                           "refl_core_check_term: succeeded with no guard\n");
                                      ((), []))
                                 | FStar_Pervasives.Inl
                                     (FStar_Pervasives_Native.Some guard) ->
                                     (dbg_refl g1
                                        (fun uu___5 ->
                                           "refl_core_check_term: succeeded with guard\n");
                                      ((), [(g1, guard)]))
                                 | FStar_Pervasives.Inr err ->
                                     (dbg_refl g1
                                        (fun uu___5 ->
                                           let uu___6 =
                                             FStar_TypeChecker_Core.print_error
                                               err in
                                           FStar_Compiler_Util.format1
                                             "refl_core_check_term failed: %s\n"
                                             uu___6);
                                      (let uu___5 =
                                         let uu___6 =
                                           let uu___7 =
                                             FStar_TypeChecker_Core.print_error
                                               err in
                                           Prims.strcat
                                             "refl_core_check_term failed: "
                                             uu___7 in
                                         (FStar_Errors_Codes.Fatal_IllTyped,
                                           uu___6) in
                                       let uu___6 =
                                         FStar_TypeChecker_Env.get_range g1 in
                                       FStar_Errors.raise_error uu___5 uu___6))))))
                   else
                     Obj.magic
                       (Obj.repr
                          (let uu___2 =
                             let uu___3 =
                               let uu___4 =
                                 let uu___5 =
                                   FStar_TypeChecker_Env.get_range g in
                                 unexpected_uvars_issue uu___5 in
                               [uu___4] in
                             (FStar_Pervasives_Native.None, uu___3) in
                           FStar_Class_Monad.return
                             FStar_Tactics_Monad.monad_tac ()
                             (Obj.magic uu___2)))) uu___3 uu___2 uu___1 uu___
let (refl_core_check_term_at_type :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_TypeChecker_Core.tot_or_ghost FStar_Pervasives_Native.option *
          issues) FStar_Tactics_Monad.tac)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun e ->
             fun t ->
               let uu___ =
                 ((no_uvars_in_g g) && (no_uvars_in_term e)) &&
                   (no_uvars_in_term t) in
               if uu___
               then
                 Obj.magic
                   (Obj.repr
                      (refl_typing_builtin_wrapper
                         "refl_core_check_term_at_type"
                         (fun uu___1 ->
                            let g1 =
                              FStar_TypeChecker_Env.set_range g
                                e.FStar_Syntax_Syntax.pos in
                            dbg_refl g1
                              (fun uu___3 ->
                                 let uu___4 =
                                   FStar_Class_Show.show
                                     FStar_Syntax_Print.showable_term e in
                                 let uu___5 =
                                   FStar_Class_Show.show
                                     FStar_Syntax_Print.showable_term t in
                                 FStar_Compiler_Util.format2
                                   "refl_core_check_term_at_type: term: %s, type: %s\n"
                                   uu___4 uu___5);
                            (let uu___3 =
                               FStar_TypeChecker_Core.check_term_at_type g1 e
                                 t in
                             match uu___3 with
                             | FStar_Pervasives.Inl
                                 (eff, FStar_Pervasives_Native.None) ->
                                 (dbg_refl g1
                                    (fun uu___5 ->
                                       FStar_Compiler_Util.format1
                                         "refl_core_check_term_at_type: succeeded with eff %s and no guard\n"
                                         (tot_or_ghost_to_string eff));
                                  (eff, []))
                             | FStar_Pervasives.Inl
                                 (eff, FStar_Pervasives_Native.Some guard) ->
                                 (dbg_refl g1
                                    (fun uu___5 ->
                                       FStar_Compiler_Util.format1
                                         "refl_core_check_term_at_type: succeeded with eff %s and guard\n"
                                         (tot_or_ghost_to_string eff));
                                  (eff, [(g1, guard)]))
                             | FStar_Pervasives.Inr err ->
                                 (dbg_refl g1
                                    (fun uu___5 ->
                                       let uu___6 =
                                         FStar_TypeChecker_Core.print_error
                                           err in
                                       FStar_Compiler_Util.format1
                                         "refl_core_check_term_at_type failed: %s\n"
                                         uu___6);
                                  (let uu___5 =
                                     let uu___6 =
                                       let uu___7 =
                                         FStar_TypeChecker_Core.print_error
                                           err in
                                       Prims.strcat
                                         "refl_core_check_term failed: "
                                         uu___7 in
                                     (FStar_Errors_Codes.Fatal_IllTyped,
                                       uu___6) in
                                   let uu___6 =
                                     FStar_TypeChecker_Env.get_range g1 in
                                   FStar_Errors.raise_error uu___5 uu___6))))))
               else
                 Obj.magic
                   (Obj.repr
                      (let uu___2 =
                         let uu___3 =
                           let uu___4 =
                             let uu___5 = FStar_TypeChecker_Env.get_range g in
                             unexpected_uvars_issue uu___5 in
                           [uu___4] in
                         (FStar_Pervasives_Native.None, uu___3) in
                       FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                         () (Obj.magic uu___2)))) uu___2 uu___1 uu___
let (refl_tc_term :
  env ->
    FStar_Syntax_Syntax.term ->
      ((FStar_Syntax_Syntax.term * (FStar_TypeChecker_Core.tot_or_ghost *
        FStar_Syntax_Syntax.typ)) FStar_Pervasives_Native.option * issues)
        FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun e ->
           let uu___ = (no_uvars_in_g g) && (no_uvars_in_term e) in
           if uu___
           then
             Obj.magic
               (Obj.repr
                  (refl_typing_builtin_wrapper "refl_tc_term"
                     (fun uu___1 ->
                        let g1 =
                          FStar_TypeChecker_Env.set_range g
                            e.FStar_Syntax_Syntax.pos in
                        dbg_refl g1
                          (fun uu___3 ->
                             let uu___4 =
                               FStar_Class_Show.show
                                 FStar_Compiler_Range_Ops.show_range
                                 e.FStar_Syntax_Syntax.pos in
                             let uu___5 =
                               FStar_Class_Show.show
                                 FStar_Syntax_Print.showable_term e in
                             FStar_Compiler_Util.format2
                               "refl_tc_term@%s: %s\n" uu___4 uu___5);
                        dbg_refl g1
                          (fun uu___4 -> "refl_tc_term: starting tc {\n");
                        (let g2 =
                           {
                             FStar_TypeChecker_Env.solver =
                               (g1.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (g1.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (g1.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (g1.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (g1.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (g1.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (g1.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (g1.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (g1.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (g1.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp = false;
                             FStar_TypeChecker_Env.effects =
                               (g1.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (g1.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (g1.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (g1.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (g1.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (g1.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (g1.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (g1.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (g1.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (g1.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (g1.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (g1.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (g1.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (g1.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.intactics =
                               (g1.FStar_TypeChecker_Env.intactics);
                             FStar_TypeChecker_Env.nocoerce =
                               (g1.FStar_TypeChecker_Env.nocoerce);
                             FStar_TypeChecker_Env.tc_term =
                               (g1.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                               (g1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                             FStar_TypeChecker_Env.universe_of =
                               (g1.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                               =
                               (g1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                             FStar_TypeChecker_Env.teq_nosmt_force =
                               (g1.FStar_TypeChecker_Env.teq_nosmt_force);
                             FStar_TypeChecker_Env.subtype_nosmt_force =
                               (g1.FStar_TypeChecker_Env.subtype_nosmt_force);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (g1.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (g1.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (g1.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (g1.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (g1.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (g1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (g1.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (g1.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (g1.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (g1.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (g1.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (g1.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (g1.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (g1.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (g1.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (g1.FStar_TypeChecker_Env.enable_defer_to_tac);
                             FStar_TypeChecker_Env.unif_allow_ref_guards =
                               (g1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                             FStar_TypeChecker_Env.erase_erasable_args =
                               (g1.FStar_TypeChecker_Env.erase_erasable_args);
                             FStar_TypeChecker_Env.core_check =
                               (g1.FStar_TypeChecker_Env.core_check)
                           } in
                         let e1 =
                           let g3 =
                             {
                               FStar_TypeChecker_Env.solver =
                                 (g2.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (g2.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (g2.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (g2.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (g2.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (g2.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (g2.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (g2.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (g2.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (g2.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (g2.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (g2.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (g2.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (g2.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (g2.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (g2.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq_strict =
                                 (g2.FStar_TypeChecker_Env.use_eq_strict);
                               FStar_TypeChecker_Env.is_iface =
                                 (g2.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (g2.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (g2.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 = true;
                               FStar_TypeChecker_Env.failhard =
                                 (g2.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (g2.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (g2.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.intactics =
                                 (g2.FStar_TypeChecker_Env.intactics);
                               FStar_TypeChecker_Env.nocoerce =
                                 (g2.FStar_TypeChecker_Env.nocoerce);
                               FStar_TypeChecker_Env.tc_term =
                                 (g2.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                 =
                                 (g2.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                               FStar_TypeChecker_Env.universe_of =
                                 (g2.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                 =
                                 (g2.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                               FStar_TypeChecker_Env.teq_nosmt_force =
                                 (g2.FStar_TypeChecker_Env.teq_nosmt_force);
                               FStar_TypeChecker_Env.subtype_nosmt_force =
                                 (g2.FStar_TypeChecker_Env.subtype_nosmt_force);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (g2.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (g2.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (g2.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (g2.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (g2.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (g2.FStar_TypeChecker_Env.try_solve_implicits_hook);
                               FStar_TypeChecker_Env.splice =
                                 (g2.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.mpreprocess =
                                 (g2.FStar_TypeChecker_Env.mpreprocess);
                               FStar_TypeChecker_Env.postprocess =
                                 (g2.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.identifier_info =
                                 (g2.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (g2.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (g2.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (g2.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (g2.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (g2.FStar_TypeChecker_Env.erasable_types_tab);
                               FStar_TypeChecker_Env.enable_defer_to_tac =
                                 (g2.FStar_TypeChecker_Env.enable_defer_to_tac);
                               FStar_TypeChecker_Env.unif_allow_ref_guards =
                                 (g2.FStar_TypeChecker_Env.unif_allow_ref_guards);
                               FStar_TypeChecker_Env.erase_erasable_args =
                                 (g2.FStar_TypeChecker_Env.erase_erasable_args);
                               FStar_TypeChecker_Env.core_check =
                                 (g2.FStar_TypeChecker_Env.core_check)
                             } in
                           let must_tot = false in
                           let uu___4 =
                             g3.FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                               g3 e must_tot in
                           match uu___4 with
                           | (e2, uu___5, guard) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard g3
                                  guard;
                                e2) in
                         try
                           (fun uu___4 ->
                              match () with
                              | () ->
                                  let uu___5 =
                                    let uu___6 = no_uvars_in_term e1 in
                                    Prims.op_Negation uu___6 in
                                  if uu___5
                                  then
                                    let uu___6 =
                                      let uu___7 =
                                        let uu___8 =
                                          FStar_Class_Show.show
                                            FStar_Syntax_Print.showable_term
                                            e1 in
                                        FStar_Compiler_Util.format1
                                          "Elaborated term has unresolved implicits: %s"
                                          uu___8 in
                                      (FStar_Errors_Codes.Error_UnexpectedUnresolvedUvar,
                                        uu___7) in
                                    FStar_Errors.raise_error uu___6
                                      e1.FStar_Syntax_Syntax.pos
                                  else
                                    (let allow_uvars = false in
                                     let allow_names = true in
                                     let e2 =
                                       FStar_Syntax_Compress.deep_compress
                                         allow_uvars allow_names e1 in
                                     dbg_refl g2
                                       (fun uu___8 ->
                                          let uu___9 =
                                            FStar_Class_Show.show
                                              FStar_Syntax_Print.showable_term
                                              e2 in
                                          FStar_Compiler_Util.format1
                                            "} finished tc with e = %s\n"
                                            uu___9);
                                     (let guards =
                                        FStar_Compiler_Util.mk_ref [] in
                                      let gh g3 guard =
                                        dbg_refl g3
                                          (fun uu___9 ->
                                             let uu___10 =
                                               let uu___11 =
                                                 FStar_TypeChecker_Env.get_range
                                                   g3 in
                                               FStar_Class_Show.show
                                                 FStar_Compiler_Range_Ops.show_range
                                                 uu___11 in
                                             let uu___11 =
                                               FStar_Class_Show.show
                                                 FStar_Syntax_Print.showable_term
                                                 guard in
                                             let uu___12 =
                                               FStar_Class_Show.show
                                                 FStar_Compiler_Range_Ops.show_range
                                                 guard.FStar_Syntax_Syntax.pos in
                                             FStar_Compiler_Util.format3
                                               "Got guard in Env@%s |- %s@%s\n"
                                               uu___10 uu___11 uu___12);
                                        (let uu___10 =
                                           let uu___11 =
                                             FStar_Compiler_Effect.op_Bang
                                               guards in
                                           (g3, guard) :: uu___11 in
                                         FStar_Compiler_Effect.op_Colon_Equals
                                           guards uu___10);
                                        true in
                                      let uu___8 =
                                        FStar_TypeChecker_Core.compute_term_type_handle_guards
                                          g2 e2 gh in
                                      match uu___8 with
                                      | FStar_Pervasives.Inl (eff, t) ->
                                          let t1 = refl_norm_type g2 t in
                                          (dbg_refl g2
                                             (fun uu___10 ->
                                                let uu___11 =
                                                  FStar_Class_Show.show
                                                    FStar_Compiler_Range_Ops.show_range
                                                    e2.FStar_Syntax_Syntax.pos in
                                                let uu___12 =
                                                  FStar_Class_Show.show
                                                    FStar_Syntax_Print.showable_term
                                                    e2 in
                                                let uu___13 =
                                                  FStar_Class_Show.show
                                                    FStar_Syntax_Print.showable_term
                                                    t1 in
                                                FStar_Compiler_Util.format3
                                                  "refl_tc_term@%s for %s computed type %s\n"
                                                  uu___11 uu___12 uu___13);
                                           (let uu___10 =
                                              FStar_Compiler_Effect.op_Bang
                                                guards in
                                            ((e2, (eff, t1)), uu___10)))
                                      | FStar_Pervasives.Inr err ->
                                          (dbg_refl g2
                                             (fun uu___10 ->
                                                let uu___11 =
                                                  FStar_TypeChecker_Core.print_error
                                                    err in
                                                FStar_Compiler_Util.format1
                                                  "refl_tc_term failed: %s\n"
                                                  uu___11);
                                           (let uu___10 =
                                              let uu___11 =
                                                let uu___12 =
                                                  FStar_TypeChecker_Core.print_error
                                                    err in
                                                Prims.strcat
                                                  "tc_term callback failed: "
                                                  uu___12 in
                                              (FStar_Errors_Codes.Fatal_IllTyped,
                                                uu___11) in
                                            FStar_Errors.raise_error uu___10
                                              e2.FStar_Syntax_Syntax.pos)))))
                             ()
                         with
                         | FStar_Errors.Error
                             (FStar_Errors_Codes.Error_UnexpectedUnresolvedUvar,
                              uu___5, uu___6, uu___7)
                             ->
                             FStar_Errors.raise_error
                               (FStar_Errors_Codes.Fatal_IllTyped,
                                 "UVars remaing in term after tc_term callback")
                               e1.FStar_Syntax_Syntax.pos))))
           else
             Obj.magic
               (Obj.repr
                  (let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 = FStar_TypeChecker_Env.get_range g in
                         unexpected_uvars_issue uu___5 in
                       [uu___4] in
                     (FStar_Pervasives_Native.None, uu___3) in
                   FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                     (Obj.magic uu___2)))) uu___1 uu___
let (refl_universe_of :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option * issues)
        FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun e ->
           let check_univ_var_resolved g1 u =
             let uu___ = FStar_Syntax_Subst.compress_univ u in
             match uu___ with
             | FStar_Syntax_Syntax.U_unif uu___1 ->
                 let uu___2 = FStar_TypeChecker_Env.get_range g1 in
                 FStar_Errors.raise_error
                   (FStar_Errors_Codes.Fatal_IllTyped,
                     "Unresolved variable in universe_of callback") uu___2
             | u1 -> u1 in
           let uu___ = (no_uvars_in_g g) && (no_uvars_in_term e) in
           if uu___
           then
             Obj.magic
               (Obj.repr
                  (refl_typing_builtin_wrapper "refl_universe_of"
                     (fun uu___1 ->
                        let g1 =
                          FStar_TypeChecker_Env.set_range g
                            e.FStar_Syntax_Syntax.pos in
                        let uu___2 = FStar_Syntax_Util.type_u () in
                        match uu___2 with
                        | (t, u) ->
                            let must_tot = false in
                            let uu___3 =
                              FStar_TypeChecker_Core.check_term g1 e t
                                must_tot in
                            (match uu___3 with
                             | FStar_Pervasives.Inl
                                 (FStar_Pervasives_Native.None) ->
                                 let uu___4 = check_univ_var_resolved g1 u in
                                 (uu___4, [])
                             | FStar_Pervasives.Inl
                                 (FStar_Pervasives_Native.Some guard) ->
                                 let uu___4 = check_univ_var_resolved g1 u in
                                 (uu___4, [(g1, guard)])
                             | FStar_Pervasives.Inr err ->
                                 (dbg_refl g1
                                    (fun uu___5 ->
                                       let uu___6 =
                                         FStar_TypeChecker_Core.print_error
                                           err in
                                       FStar_Compiler_Util.format1
                                         "refl_universe_of failed: %s\n"
                                         uu___6);
                                  (let uu___5 =
                                     let uu___6 =
                                       let uu___7 =
                                         FStar_TypeChecker_Core.print_error
                                           err in
                                       Prims.strcat "universe_of failed: "
                                         uu___7 in
                                     (FStar_Errors_Codes.Fatal_IllTyped,
                                       uu___6) in
                                   let uu___6 =
                                     FStar_TypeChecker_Env.get_range g1 in
                                   FStar_Errors.raise_error uu___5 uu___6))))))
           else
             Obj.magic
               (Obj.repr
                  (let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 = FStar_TypeChecker_Env.get_range g in
                         unexpected_uvars_issue uu___5 in
                       [uu___4] in
                     (FStar_Pervasives_Native.None, uu___3) in
                   FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                     (Obj.magic uu___2)))) uu___1 uu___
let (refl_check_prop_validity :
  env ->
    FStar_Syntax_Syntax.term ->
      (unit FStar_Pervasives_Native.option * issues) FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun e ->
           let uu___ = (no_uvars_in_g g) && (no_uvars_in_term e) in
           if uu___
           then
             Obj.magic
               (Obj.repr
                  (refl_typing_builtin_wrapper "refl_check_prop_validity"
                     (fun uu___1 ->
                        let g1 =
                          FStar_TypeChecker_Env.set_range g
                            e.FStar_Syntax_Syntax.pos in
                        dbg_refl g1
                          (fun uu___3 ->
                             let uu___4 =
                               FStar_Class_Show.show
                                 FStar_Syntax_Print.showable_term e in
                             FStar_Compiler_Util.format1
                               "refl_check_prop_validity: %s\n" uu___4);
                        (let must_tot = false in
                         (let uu___4 =
                            let uu___5 =
                              FStar_Syntax_Util.fvar_const
                                FStar_Parser_Const.prop_lid in
                            FStar_TypeChecker_Core.check_term g1 e uu___5
                              must_tot in
                          match uu___4 with
                          | FStar_Pervasives.Inl
                              (FStar_Pervasives_Native.None) -> ()
                          | FStar_Pervasives.Inl
                              (FStar_Pervasives_Native.Some guard) ->
                              FStar_TypeChecker_Rel.force_trivial_guard g1
                                {
                                  FStar_TypeChecker_Common.guard_f =
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard);
                                  FStar_TypeChecker_Common.deferred_to_tac =
                                    (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred_to_tac);
                                  FStar_TypeChecker_Common.deferred =
                                    (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred);
                                  FStar_TypeChecker_Common.univ_ineqs =
                                    (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.univ_ineqs);
                                  FStar_TypeChecker_Common.implicits =
                                    (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.implicits)
                                }
                          | FStar_Pervasives.Inr err ->
                              let msg =
                                let uu___5 =
                                  FStar_TypeChecker_Core.print_error err in
                                FStar_Compiler_Util.format1
                                  "refl_check_prop_validity failed (not a prop): %s\n"
                                  uu___5 in
                              (dbg_refl g1 (fun uu___6 -> msg);
                               (let uu___6 =
                                  FStar_TypeChecker_Env.get_range g1 in
                                FStar_Errors.raise_error
                                  (FStar_Errors_Codes.Fatal_IllTyped, msg)
                                  uu___6)));
                         ((), [(g1, e)])))))
           else
             Obj.magic
               (Obj.repr
                  (let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 = FStar_TypeChecker_Env.get_range g in
                         unexpected_uvars_issue uu___5 in
                       [uu___4] in
                     (FStar_Pervasives_Native.None, uu___3) in
                   FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                     (Obj.magic uu___2)))) uu___1 uu___
let (refl_check_match_complete :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Reflection_V2_Data.pattern Prims.list ->
          (FStar_Reflection_V2_Data.pattern Prims.list *
            FStar_Reflection_V2_Data.binding Prims.list Prims.list)
            FStar_Pervasives_Native.option FStar_Tactics_Monad.tac)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun sc ->
               fun scty ->
                 fun pats ->
                   let uu___ =
                     FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.repr ()) in
                   Obj.magic
                     (FStar_Class_Monad.op_let_Bang
                        FStar_Tactics_Monad.monad_tac () () uu___
                        (fun uu___1 ->
                           (fun uu___1 ->
                              let uu___1 = Obj.magic uu___1 in
                              let one = FStar_Syntax_Util.exp_int "1" in
                              let brs =
                                FStar_Compiler_List.map
                                  (fun p ->
                                     let p1 =
                                       FStar_Reflection_V2_Builtins.pack_pat
                                         p in
                                     (p1, FStar_Pervasives_Native.None, one))
                                  pats in
                              let mm =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_match
                                     {
                                       FStar_Syntax_Syntax.scrutinee = sc;
                                       FStar_Syntax_Syntax.ret_opt =
                                         FStar_Pervasives_Native.None;
                                       FStar_Syntax_Syntax.brs = brs;
                                       FStar_Syntax_Syntax.rc_opt1 =
                                         FStar_Pervasives_Native.None
                                     }) sc.FStar_Syntax_Syntax.pos in
                              let env1 = g in
                              let env2 =
                                FStar_TypeChecker_Env.set_expected_typ env1
                                  FStar_Syntax_Syntax.t_int in
                              let uu___2 = __tc env2 mm in
                              Obj.magic
                                (FStar_Class_Monad.op_let_Bang
                                   FStar_Tactics_Monad.monad_tac () ()
                                   (Obj.magic uu___2)
                                   (fun uu___3 ->
                                      (fun uu___3 ->
                                         let uu___3 = Obj.magic uu___3 in
                                         match uu___3 with
                                         | (mm1, uu___4, g1) ->
                                             let uu___5 =
                                               FStar_Errors.catch_errors_and_ignore_rest
                                                 (fun uu___6 ->
                                                    let uu___7 =
                                                      FStar_TypeChecker_Rel.discharge_guard
                                                        env2 g1 in
                                                    FStar_TypeChecker_Env.is_trivial
                                                      uu___7) in
                                             (match uu___5 with
                                              | (errs, b) ->
                                                  (match (errs, b) with
                                                   | ([],
                                                      FStar_Pervasives_Native.Some
                                                      (true)) ->
                                                       let get_pats t =
                                                         let uu___6 =
                                                           let uu___7 =
                                                             FStar_Syntax_Util.unmeta
                                                               t in
                                                           uu___7.FStar_Syntax_Syntax.n in
                                                         match uu___6 with
                                                         | FStar_Syntax_Syntax.Tm_match
                                                             {
                                                               FStar_Syntax_Syntax.scrutinee
                                                                 = uu___7;
                                                               FStar_Syntax_Syntax.ret_opt
                                                                 = uu___8;
                                                               FStar_Syntax_Syntax.brs
                                                                 = brs1;
                                                               FStar_Syntax_Syntax.rc_opt1
                                                                 = uu___9;_}
                                                             ->
                                                             FStar_Compiler_List.map
                                                               (fun uu___10
                                                                  ->
                                                                  match uu___10
                                                                  with
                                                                  | (p,
                                                                    uu___11,
                                                                    uu___12)
                                                                    -> p)
                                                               brs1
                                                         | uu___7 ->
                                                             FStar_Compiler_Effect.failwith
                                                               "refl_check_match_complete: not a match?" in
                                                       let pats1 =
                                                         get_pats mm1 in
                                                       let rec bnds_for_pat p
                                                         =
                                                         match p.FStar_Syntax_Syntax.v
                                                         with
                                                         | FStar_Syntax_Syntax.Pat_constant
                                                             uu___6 -> []
                                                         | FStar_Syntax_Syntax.Pat_cons
                                                             (fv, uu___6,
                                                              pats2)
                                                             ->
                                                             FStar_Compiler_List.concatMap
                                                               (fun uu___7 ->
                                                                  match uu___7
                                                                  with
                                                                  | (p1,
                                                                    uu___8)
                                                                    ->
                                                                    bnds_for_pat
                                                                    p1) pats2
                                                         | FStar_Syntax_Syntax.Pat_var
                                                             bv ->
                                                             let uu___6 =
                                                               bv_to_binding
                                                                 bv in
                                                             [uu___6]
                                                         | FStar_Syntax_Syntax.Pat_dot_term
                                                             uu___6 -> [] in
                                                       let uu___6 =
                                                         let uu___7 =
                                                           let uu___8 =
                                                             FStar_Compiler_List.map
                                                               FStar_Reflection_V2_Builtins.inspect_pat
                                                               pats1 in
                                                           let uu___9 =
                                                             FStar_Compiler_List.map
                                                               bnds_for_pat
                                                               pats1 in
                                                           (uu___8, uu___9) in
                                                         FStar_Pervasives_Native.Some
                                                           uu___7 in
                                                       Obj.magic
                                                         (FStar_Class_Monad.return
                                                            FStar_Tactics_Monad.monad_tac
                                                            ()
                                                            (Obj.magic uu___6))
                                                   | uu___6 ->
                                                       Obj.magic
                                                         (FStar_Class_Monad.return
                                                            FStar_Tactics_Monad.monad_tac
                                                            ()
                                                            (Obj.magic
                                                               FStar_Pervasives_Native.None)))))
                                        uu___3))) uu___1))) uu___3 uu___2
            uu___1 uu___
let (refl_instantiate_implicits :
  env ->
    FStar_Syntax_Syntax.term ->
      (((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.typ) Prims.list *
        FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option * issues) FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun e ->
           let uu___ = (no_uvars_in_g g) && (no_uvars_in_term e) in
           if uu___
           then
             Obj.magic
               (Obj.repr
                  (refl_typing_builtin_wrapper "refl_instantiate_implicits"
                     (fun uu___1 ->
                        let g1 =
                          FStar_TypeChecker_Env.set_range g
                            e.FStar_Syntax_Syntax.pos in
                        dbg_refl g1
                          (fun uu___3 ->
                             let uu___4 =
                               FStar_Class_Show.show
                                 FStar_Syntax_Print.showable_term e in
                             FStar_Compiler_Util.format1
                               "refl_instantiate_implicits: %s\n" uu___4);
                        dbg_refl g1
                          (fun uu___4 ->
                             "refl_instantiate_implicits: starting tc {\n");
                        (let must_tot = false in
                         let g2 =
                           {
                             FStar_TypeChecker_Env.solver =
                               (g1.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (g1.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (g1.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (g1.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (g1.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (g1.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (g1.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (g1.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (g1.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (g1.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp = false;
                             FStar_TypeChecker_Env.effects =
                               (g1.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (g1.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (g1.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (g1.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (g1.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (g1.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (g1.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (g1.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (g1.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 = true;
                             FStar_TypeChecker_Env.failhard =
                               (g1.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (g1.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (g1.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.intactics =
                               (g1.FStar_TypeChecker_Env.intactics);
                             FStar_TypeChecker_Env.nocoerce =
                               (g1.FStar_TypeChecker_Env.nocoerce);
                             FStar_TypeChecker_Env.tc_term =
                               (g1.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                               (g1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                             FStar_TypeChecker_Env.universe_of =
                               (g1.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                               =
                               (g1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                             FStar_TypeChecker_Env.teq_nosmt_force =
                               (g1.FStar_TypeChecker_Env.teq_nosmt_force);
                             FStar_TypeChecker_Env.subtype_nosmt_force =
                               (g1.FStar_TypeChecker_Env.subtype_nosmt_force);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (g1.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (g1.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (g1.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (g1.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (g1.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (g1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (g1.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (g1.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (g1.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (g1.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (g1.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (g1.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (g1.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (g1.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (g1.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (g1.FStar_TypeChecker_Env.enable_defer_to_tac);
                             FStar_TypeChecker_Env.unif_allow_ref_guards =
                               (g1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                             FStar_TypeChecker_Env.erase_erasable_args =
                               (g1.FStar_TypeChecker_Env.erase_erasable_args);
                             FStar_TypeChecker_Env.core_check =
                               (g1.FStar_TypeChecker_Env.core_check)
                           } in
                         let uu___4 =
                           g2.FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                             g2 e must_tot in
                         match uu___4 with
                         | (e1, t, guard) ->
                             let guard1 =
                               let uu___5 =
                                 FStar_TypeChecker_Rel.solve_deferred_constraints
                                   g2 guard in
                               FStar_TypeChecker_Rel.resolve_implicits g2
                                 uu___5 in
                             let bvs_and_ts =
                               match guard1.FStar_TypeChecker_Common.implicits
                               with
                               | [] -> []
                               | uu___5 ->
                                   let l =
                                     FStar_Compiler_List.map
                                       (fun uu___6 ->
                                          match uu___6 with
                                          | {
                                              FStar_TypeChecker_Common.imp_reason
                                                = uu___7;
                                              FStar_TypeChecker_Common.imp_uvar
                                                = imp_uvar;
                                              FStar_TypeChecker_Common.imp_tm
                                                = uu___8;
                                              FStar_TypeChecker_Common.imp_range
                                                = uu___9;_}
                                              ->
                                              let uu___10 =
                                                FStar_Syntax_Util.ctx_uvar_typ
                                                  imp_uvar in
                                              let uu___11 =
                                                let uu___12 =
                                                  FStar_Syntax_Syntax.mk
                                                    FStar_Syntax_Syntax.Tm_unknown
                                                    FStar_Compiler_Range_Type.dummyRange in
                                                FStar_Syntax_Syntax.new_bv
                                                  FStar_Pervasives_Native.None
                                                  uu___12 in
                                              ((imp_uvar.FStar_Syntax_Syntax.ctx_uvar_head),
                                                uu___10, uu___11))
                                       guard1.FStar_TypeChecker_Common.implicits in
                                   (FStar_Compiler_List.iter
                                      (fun uu___7 ->
                                         match uu___7 with
                                         | (uv, uu___8, bv) ->
                                             let uu___9 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 bv in
                                             FStar_Syntax_Util.set_uvar uv
                                               uu___9) l;
                                    FStar_Compiler_List.map
                                      (fun uu___7 ->
                                         match uu___7 with
                                         | (uu___8, t1, bv) -> (bv, t1)) l) in
                             (dbg_refl g2
                                (fun uu___6 ->
                                   let uu___7 =
                                     FStar_Class_Show.show
                                       FStar_Syntax_Print.showable_term e1 in
                                   let uu___8 =
                                     FStar_Class_Show.show
                                       FStar_Syntax_Print.showable_term t in
                                   FStar_Compiler_Util.format2
                                     "refl_instantiate_implicits: inferred %s : %s"
                                     uu___7 uu___8);
                              (let uu___7 =
                                 let uu___8 = no_univ_uvars_in_term e1 in
                                 Prims.op_Negation uu___8 in
                               if uu___7
                               then
                                 let uu___8 =
                                   let uu___9 =
                                     let uu___10 =
                                       FStar_Class_Show.show
                                         FStar_Syntax_Print.showable_term e1 in
                                     FStar_Compiler_Util.format1
                                       "Elaborated term has unresolved univ uvars: %s"
                                       uu___10 in
                                   (FStar_Errors_Codes.Error_UnexpectedUnresolvedUvar,
                                     uu___9) in
                                 FStar_Errors.raise_error uu___8
                                   e1.FStar_Syntax_Syntax.pos
                               else ());
                              (let uu___8 =
                                 let uu___9 = no_univ_uvars_in_term t in
                                 Prims.op_Negation uu___9 in
                               if uu___8
                               then
                                 let uu___9 =
                                   let uu___10 =
                                     let uu___11 =
                                       FStar_Class_Show.show
                                         FStar_Syntax_Print.showable_term t in
                                     FStar_Compiler_Util.format1
                                       "Inferred type has unresolved univ uvars: %s"
                                       uu___11 in
                                   (FStar_Errors_Codes.Error_UnexpectedUnresolvedUvar,
                                     uu___10) in
                                 FStar_Errors.raise_error uu___9
                                   e1.FStar_Syntax_Syntax.pos
                               else ());
                              FStar_Compiler_List.iter
                                (fun uu___9 ->
                                   match uu___9 with
                                   | (x, t1) ->
                                       let uu___10 =
                                         let uu___11 =
                                           no_univ_uvars_in_term t1 in
                                         Prims.op_Negation uu___11 in
                                       if uu___10
                                       then
                                         let uu___11 =
                                           let uu___12 =
                                             let uu___13 =
                                               FStar_Class_Show.show
                                                 FStar_Syntax_Print.showable_bv
                                                 x in
                                             let uu___14 =
                                               FStar_Class_Show.show
                                                 FStar_Syntax_Print.showable_term
                                                 t1 in
                                             FStar_Compiler_Util.format2
                                               "Inferred type has unresolved univ uvars:  %s:%s"
                                               uu___13 uu___14 in
                                           (FStar_Errors_Codes.Error_UnexpectedUnresolvedUvar,
                                             uu___12) in
                                         FStar_Errors.raise_error uu___11
                                           e1.FStar_Syntax_Syntax.pos
                                       else ()) bvs_and_ts;
                              (let g3 =
                                 let uu___9 =
                                   FStar_Compiler_List.map
                                     (fun uu___10 ->
                                        match uu___10 with
                                        | (bv, t1) ->
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (bv.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (bv.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            }) bvs_and_ts in
                                 FStar_TypeChecker_Env.push_bvs g2 uu___9 in
                               let allow_uvars = false in
                               let allow_names = true in
                               let e2 =
                                 FStar_Syntax_Compress.deep_compress
                                   allow_uvars allow_names e1 in
                               let t1 =
                                 let uu___9 = refl_norm_type g3 t in
                                 FStar_Syntax_Compress.deep_compress
                                   allow_uvars allow_names uu___9 in
                               let bvs_and_ts1 =
                                 FStar_Compiler_List.map
                                   (fun uu___9 ->
                                      match uu___9 with
                                      | (bv, t2) ->
                                          let uu___10 =
                                            FStar_Syntax_Compress.deep_compress
                                              allow_uvars allow_names t2 in
                                          (bv, uu___10)) bvs_and_ts in
                               dbg_refl g3
                                 (fun uu___10 ->
                                    let uu___11 =
                                      FStar_Class_Show.show
                                        FStar_Syntax_Print.showable_term e2 in
                                    let uu___12 =
                                      FStar_Class_Show.show
                                        FStar_Syntax_Print.showable_term t1 in
                                    FStar_Compiler_Util.format2
                                      "} finished tc with e = %s and t = %s\n"
                                      uu___11 uu___12);
                               ((bvs_and_ts1, e2, t1), [])))))))
           else
             Obj.magic
               (Obj.repr
                  (let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 = FStar_TypeChecker_Env.get_range g in
                         unexpected_uvars_issue uu___5 in
                       [uu___4] in
                     (FStar_Pervasives_Native.None, uu___3) in
                   FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                     (Obj.magic uu___2)))) uu___1 uu___
let (refl_try_unify :
  env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.typ) Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) Prims.list
            FStar_Pervasives_Native.option * issues) FStar_Tactics_Monad.tac)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun uvs ->
               fun t0 ->
                 fun t1 ->
                   let uu___ =
                     (((no_uvars_in_g g) && (no_uvars_in_term t0)) &&
                        (no_uvars_in_term t1))
                       &&
                       (let uu___1 =
                          FStar_Compiler_List.map FStar_Pervasives_Native.snd
                            uvs in
                        FStar_Compiler_List.for_all no_uvars_in_term uu___1) in
                   if uu___
                   then
                     Obj.magic
                       (Obj.repr
                          (refl_typing_builtin_wrapper "refl_try_unify"
                             (fun uu___1 ->
                                dbg_refl g
                                  (fun uu___3 ->
                                     let uu___4 =
                                       FStar_Class_Show.show
                                         FStar_Syntax_Print.showable_term t0 in
                                     let uu___5 =
                                       FStar_Class_Show.show
                                         FStar_Syntax_Print.showable_term t1 in
                                     let uu___6 =
                                       FStar_Class_Show.show
                                         (FStar_Class_Show.show_list
                                            (FStar_Class_Show.show_tuple2
                                               FStar_Syntax_Print.showable_bv
                                               FStar_Syntax_Print.showable_term))
                                         uvs in
                                     FStar_Compiler_Util.format3
                                       "refl_try_unify %s and %s, with uvs: %s {\n"
                                       uu___4 uu___5 uu___6);
                                (let g1 =
                                   FStar_TypeChecker_Env.set_range g
                                     t0.FStar_Syntax_Syntax.pos in
                                 let uu___3 =
                                   let uu___4 =
                                     let uu___5 =
                                       FStar_Compiler_Util.pimap_empty () in
                                     (FStar_TypeChecker_Env.trivial_guard,
                                       [], uu___5) in
                                   FStar_Compiler_List.fold_left
                                     (fun uu___5 ->
                                        fun uu___6 ->
                                          match (uu___5, uu___6) with
                                          | ((guard_uvs, ss, tbl), (bv, t))
                                              ->
                                              let t2 =
                                                FStar_Syntax_Subst.subst ss t in
                                              let uu___7 =
                                                let reason =
                                                  let uu___8 =
                                                    FStar_Class_Show.show
                                                      FStar_Syntax_Print.showable_bv
                                                      bv in
                                                  FStar_Compiler_Util.format1
                                                    "refl_try_unify for %s"
                                                    uu___8 in
                                                let should_check_uvar =
                                                  FStar_Syntax_Syntax.Allow_untyped
                                                    "refl_try_unify" in
                                                FStar_TypeChecker_Env.new_implicit_var_aux
                                                  reason
                                                  t0.FStar_Syntax_Syntax.pos
                                                  g1 t2 should_check_uvar
                                                  FStar_Pervasives_Native.None in
                                              (match uu___7 with
                                               | (uv_t, (ctx_u, uu___8)::[],
                                                  guard_uv) ->
                                                   let uv_id =
                                                     FStar_Syntax_Unionfind.uvar_unique_id
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   let uu___9 =
                                                     FStar_TypeChecker_Env.conj_guard
                                                       guard_uvs guard_uv in
                                                   let uu___10 =
                                                     FStar_Compiler_Util.pimap_add
                                                       tbl uv_id
                                                       ((ctx_u.FStar_Syntax_Syntax.ctx_uvar_head),
                                                         bv) in
                                                   (uu___9,
                                                     ((FStar_Syntax_Syntax.NT
                                                         (bv, uv_t)) :: ss),
                                                     uu___10))) uu___4 uvs in
                                 match uu___3 with
                                 | (guard_uvs, ss, tbl) ->
                                     let uu___4 =
                                       let uu___5 =
                                         FStar_Syntax_Subst.subst ss t0 in
                                       let uu___6 =
                                         FStar_Syntax_Subst.subst ss t1 in
                                       (uu___5, uu___6) in
                                     (match uu___4 with
                                      | (t01, t11) ->
                                          let g2 =
                                            {
                                              FStar_TypeChecker_Env.solver =
                                                (g1.FStar_TypeChecker_Env.solver);
                                              FStar_TypeChecker_Env.range =
                                                (g1.FStar_TypeChecker_Env.range);
                                              FStar_TypeChecker_Env.curmodule
                                                =
                                                (g1.FStar_TypeChecker_Env.curmodule);
                                              FStar_TypeChecker_Env.gamma =
                                                (g1.FStar_TypeChecker_Env.gamma);
                                              FStar_TypeChecker_Env.gamma_sig
                                                =
                                                (g1.FStar_TypeChecker_Env.gamma_sig);
                                              FStar_TypeChecker_Env.gamma_cache
                                                =
                                                (g1.FStar_TypeChecker_Env.gamma_cache);
                                              FStar_TypeChecker_Env.modules =
                                                (g1.FStar_TypeChecker_Env.modules);
                                              FStar_TypeChecker_Env.expected_typ
                                                =
                                                (g1.FStar_TypeChecker_Env.expected_typ);
                                              FStar_TypeChecker_Env.sigtab =
                                                (g1.FStar_TypeChecker_Env.sigtab);
                                              FStar_TypeChecker_Env.attrtab =
                                                (g1.FStar_TypeChecker_Env.attrtab);
                                              FStar_TypeChecker_Env.instantiate_imp
                                                =
                                                (g1.FStar_TypeChecker_Env.instantiate_imp);
                                              FStar_TypeChecker_Env.effects =
                                                (g1.FStar_TypeChecker_Env.effects);
                                              FStar_TypeChecker_Env.generalize
                                                =
                                                (g1.FStar_TypeChecker_Env.generalize);
                                              FStar_TypeChecker_Env.letrecs =
                                                (g1.FStar_TypeChecker_Env.letrecs);
                                              FStar_TypeChecker_Env.top_level
                                                =
                                                (g1.FStar_TypeChecker_Env.top_level);
                                              FStar_TypeChecker_Env.check_uvars
                                                =
                                                (g1.FStar_TypeChecker_Env.check_uvars);
                                              FStar_TypeChecker_Env.use_eq_strict
                                                =
                                                (g1.FStar_TypeChecker_Env.use_eq_strict);
                                              FStar_TypeChecker_Env.is_iface
                                                =
                                                (g1.FStar_TypeChecker_Env.is_iface);
                                              FStar_TypeChecker_Env.admit =
                                                (g1.FStar_TypeChecker_Env.admit);
                                              FStar_TypeChecker_Env.lax =
                                                true;
                                              FStar_TypeChecker_Env.lax_universes
                                                =
                                                (g1.FStar_TypeChecker_Env.lax_universes);
                                              FStar_TypeChecker_Env.phase1 =
                                                true;
                                              FStar_TypeChecker_Env.failhard
                                                =
                                                (g1.FStar_TypeChecker_Env.failhard);
                                              FStar_TypeChecker_Env.nosynth =
                                                (g1.FStar_TypeChecker_Env.nosynth);
                                              FStar_TypeChecker_Env.uvar_subtyping
                                                =
                                                (g1.FStar_TypeChecker_Env.uvar_subtyping);
                                              FStar_TypeChecker_Env.intactics
                                                =
                                                (g1.FStar_TypeChecker_Env.intactics);
                                              FStar_TypeChecker_Env.nocoerce
                                                =
                                                (g1.FStar_TypeChecker_Env.nocoerce);
                                              FStar_TypeChecker_Env.tc_term =
                                                (g1.FStar_TypeChecker_Env.tc_term);
                                              FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                                =
                                                (g1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                              FStar_TypeChecker_Env.universe_of
                                                =
                                                (g1.FStar_TypeChecker_Env.universe_of);
                                              FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                =
                                                (g1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                              FStar_TypeChecker_Env.teq_nosmt_force
                                                =
                                                (g1.FStar_TypeChecker_Env.teq_nosmt_force);
                                              FStar_TypeChecker_Env.subtype_nosmt_force
                                                =
                                                (g1.FStar_TypeChecker_Env.subtype_nosmt_force);
                                              FStar_TypeChecker_Env.qtbl_name_and_index
                                                =
                                                (g1.FStar_TypeChecker_Env.qtbl_name_and_index);
                                              FStar_TypeChecker_Env.normalized_eff_names
                                                =
                                                (g1.FStar_TypeChecker_Env.normalized_eff_names);
                                              FStar_TypeChecker_Env.fv_delta_depths
                                                =
                                                (g1.FStar_TypeChecker_Env.fv_delta_depths);
                                              FStar_TypeChecker_Env.proof_ns
                                                =
                                                (g1.FStar_TypeChecker_Env.proof_ns);
                                              FStar_TypeChecker_Env.synth_hook
                                                =
                                                (g1.FStar_TypeChecker_Env.synth_hook);
                                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                                =
                                                (g1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                              FStar_TypeChecker_Env.splice =
                                                (g1.FStar_TypeChecker_Env.splice);
                                              FStar_TypeChecker_Env.mpreprocess
                                                =
                                                (g1.FStar_TypeChecker_Env.mpreprocess);
                                              FStar_TypeChecker_Env.postprocess
                                                =
                                                (g1.FStar_TypeChecker_Env.postprocess);
                                              FStar_TypeChecker_Env.identifier_info
                                                =
                                                (g1.FStar_TypeChecker_Env.identifier_info);
                                              FStar_TypeChecker_Env.tc_hooks
                                                =
                                                (g1.FStar_TypeChecker_Env.tc_hooks);
                                              FStar_TypeChecker_Env.dsenv =
                                                (g1.FStar_TypeChecker_Env.dsenv);
                                              FStar_TypeChecker_Env.nbe =
                                                (g1.FStar_TypeChecker_Env.nbe);
                                              FStar_TypeChecker_Env.strict_args_tab
                                                =
                                                (g1.FStar_TypeChecker_Env.strict_args_tab);
                                              FStar_TypeChecker_Env.erasable_types_tab
                                                =
                                                (g1.FStar_TypeChecker_Env.erasable_types_tab);
                                              FStar_TypeChecker_Env.enable_defer_to_tac
                                                =
                                                (g1.FStar_TypeChecker_Env.enable_defer_to_tac);
                                              FStar_TypeChecker_Env.unif_allow_ref_guards
                                                =
                                                (g1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                              FStar_TypeChecker_Env.erase_erasable_args
                                                =
                                                (g1.FStar_TypeChecker_Env.erase_erasable_args);
                                              FStar_TypeChecker_Env.core_check
                                                =
                                                (g1.FStar_TypeChecker_Env.core_check)
                                            } in
                                          let guard_eq =
                                            let smt_ok = true in
                                            FStar_TypeChecker_Rel.try_teq
                                              smt_ok g2 t01 t11 in
                                          let l =
                                            match guard_eq with
                                            | FStar_Pervasives_Native.None ->
                                                []
                                            | FStar_Pervasives_Native.Some
                                                guard ->
                                                let guard1 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    guard_uvs guard in
                                                let guard2 =
                                                  let uu___5 =
                                                    FStar_TypeChecker_Rel.solve_deferred_constraints
                                                      g2 guard1 in
                                                  FStar_TypeChecker_Rel.resolve_implicits
                                                    g2 uu___5 in
                                                let b =
                                                  FStar_Compiler_List.existsb
                                                    (fun uu___5 ->
                                                       match uu___5 with
                                                       | {
                                                           FStar_TypeChecker_Common.imp_reason
                                                             = uu___6;
                                                           FStar_TypeChecker_Common.imp_uvar
                                                             =
                                                             {
                                                               FStar_Syntax_Syntax.ctx_uvar_head
                                                                 =
                                                                 (uv, uu___7,
                                                                  uu___8);
                                                               FStar_Syntax_Syntax.ctx_uvar_gamma
                                                                 = uu___9;
                                                               FStar_Syntax_Syntax.ctx_uvar_binders
                                                                 = uu___10;
                                                               FStar_Syntax_Syntax.ctx_uvar_reason
                                                                 = uu___11;
                                                               FStar_Syntax_Syntax.ctx_uvar_range
                                                                 = uu___12;
                                                               FStar_Syntax_Syntax.ctx_uvar_meta
                                                                 = uu___13;_};
                                                           FStar_TypeChecker_Common.imp_tm
                                                             = uu___14;
                                                           FStar_TypeChecker_Common.imp_range
                                                             = uu___15;_}
                                                           ->
                                                           let uu___16 =
                                                             let uu___17 =
                                                               FStar_Unionfind.puf_unique_id
                                                                 uv in
                                                             FStar_Compiler_Util.pimap_try_find
                                                               tbl uu___17 in
                                                           uu___16 =
                                                             FStar_Pervasives_Native.None)
                                                    guard2.FStar_TypeChecker_Common.implicits in
                                                if b
                                                then []
                                                else
                                                  FStar_Compiler_Util.pimap_fold
                                                    tbl
                                                    (fun id ->
                                                       fun uu___6 ->
                                                         fun l1 ->
                                                           match uu___6 with
                                                           | (uvar, bv) ->
                                                               let uu___7 =
                                                                 FStar_Syntax_Unionfind.find
                                                                   uvar in
                                                               (match uu___7
                                                                with
                                                                | FStar_Pervasives_Native.Some
                                                                    t ->
                                                                    let allow_uvars
                                                                    = true in
                                                                    let allow_names
                                                                    = true in
                                                                    let t2 =
                                                                    FStar_Syntax_Compress.deep_compress
                                                                    allow_uvars
                                                                    allow_names
                                                                    t in
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStar_Syntax_Free.uvars_full
                                                                    t2 in
                                                                    FStar_Compiler_Set.is_empty
                                                                    FStar_Syntax_Free.ord_ctx_uvar
                                                                    uu___9 in
                                                                    if uu___8
                                                                    then
                                                                    (bv, t2)
                                                                    :: l1
                                                                    else l1
                                                                | FStar_Pervasives_Native.None
                                                                    -> l1))
                                                    [] in
                                          (dbg_refl g2
                                             (fun uu___6 ->
                                                let uu___7 =
                                                  FStar_Class_Show.show
                                                    (FStar_Class_Show.show_list
                                                       (FStar_Class_Show.show_tuple2
                                                          FStar_Syntax_Print.showable_bv
                                                          FStar_Syntax_Print.showable_term))
                                                    l in
                                                FStar_Compiler_Util.format1
                                                  "} refl_try_unify, substitution is: %s\n"
                                                  uu___7);
                                           (l, [])))))))
                   else
                     Obj.magic
                       (Obj.repr
                          (let uu___2 =
                             let uu___3 =
                               let uu___4 =
                                 let uu___5 =
                                   FStar_TypeChecker_Env.get_range g in
                                 unexpected_uvars_issue uu___5 in
                               [uu___4] in
                             (FStar_Pervasives_Native.None, uu___3) in
                           FStar_Class_Monad.return
                             FStar_Tactics_Monad.monad_tac ()
                             (Obj.magic uu___2)))) uu___3 uu___2 uu___1 uu___
let (refl_maybe_relate_after_unfolding :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_TypeChecker_Core.side FStar_Pervasives_Native.option * issues)
          FStar_Tactics_Monad.tac)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun t0 ->
             fun t1 ->
               let uu___ =
                 ((no_uvars_in_g g) && (no_uvars_in_term t0)) &&
                   (no_uvars_in_term t1) in
               if uu___
               then
                 Obj.magic
                   (Obj.repr
                      (refl_typing_builtin_wrapper
                         "refl_maybe_relate_after_unfolding"
                         (fun uu___1 ->
                            let g1 =
                              FStar_TypeChecker_Env.set_range g
                                t0.FStar_Syntax_Syntax.pos in
                            dbg_refl g1
                              (fun uu___3 ->
                                 let uu___4 =
                                   FStar_Class_Show.show
                                     FStar_Syntax_Print.showable_term t0 in
                                 let uu___5 =
                                   FStar_Class_Show.show
                                     FStar_Syntax_Print.showable_term t1 in
                                 FStar_Compiler_Util.format2
                                   "refl_maybe_relate_after_unfolding: %s and %s {\n"
                                   uu___4 uu___5);
                            (let s =
                               FStar_TypeChecker_Core.maybe_relate_after_unfolding
                                 g1 t0 t1 in
                             dbg_refl g1
                               (fun uu___4 ->
                                  let uu___5 =
                                    FStar_Class_Show.show
                                      FStar_TypeChecker_Core.showable_side s in
                                  FStar_Compiler_Util.format1
                                    "} returning side: %s\n" uu___5);
                             (s, [])))))
               else
                 Obj.magic
                   (Obj.repr
                      (let uu___2 =
                         let uu___3 =
                           let uu___4 =
                             let uu___5 = FStar_TypeChecker_Env.get_range g in
                             unexpected_uvars_issue uu___5 in
                           [uu___4] in
                         (FStar_Pervasives_Native.None, uu___3) in
                       FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                         () (Obj.magic uu___2)))) uu___2 uu___1 uu___
let (refl_maybe_unfold_head :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * issues)
        FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun e ->
           let uu___ = (no_uvars_in_g g) && (no_uvars_in_term e) in
           if uu___
           then
             Obj.magic
               (Obj.repr
                  (refl_typing_builtin_wrapper "refl_maybe_unfold_head"
                     (fun uu___1 ->
                        let g1 =
                          FStar_TypeChecker_Env.set_range g
                            e.FStar_Syntax_Syntax.pos in
                        dbg_refl g1
                          (fun uu___3 ->
                             let uu___4 =
                               FStar_Class_Show.show
                                 FStar_Syntax_Print.showable_term e in
                             FStar_Compiler_Util.format1
                               "refl_maybe_unfold_head: %s {\n" uu___4);
                        (let eopt =
                           FStar_TypeChecker_Normalize.maybe_unfold_head g1 e in
                         dbg_refl g1
                           (fun uu___4 ->
                              let uu___5 =
                                match eopt with
                                | FStar_Pervasives_Native.None -> "none"
                                | FStar_Pervasives_Native.Some e1 ->
                                    FStar_Class_Show.show
                                      FStar_Syntax_Print.showable_term e1 in
                              FStar_Compiler_Util.format1 "} eopt = %s\n"
                                uu___5);
                         if eopt = FStar_Pervasives_Native.None
                         then
                           (let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  FStar_Class_Show.show
                                    FStar_Syntax_Print.showable_term e in
                                FStar_Compiler_Util.format1
                                  "Could not unfold head: %s\n" uu___6 in
                              (FStar_Errors_Codes.Fatal_UnexpectedTerm,
                                uu___5) in
                            FStar_Errors.raise_error uu___4
                              e.FStar_Syntax_Syntax.pos)
                         else
                           (let uu___5 = FStar_Compiler_Util.must eopt in
                            (uu___5, []))))))
           else
             Obj.magic
               (Obj.repr
                  (let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 = FStar_TypeChecker_Env.get_range g in
                         unexpected_uvars_issue uu___5 in
                       [uu___4] in
                     (FStar_Pervasives_Native.None, uu___3) in
                   FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                     (Obj.magic uu___2)))) uu___1 uu___
let (push_open_namespace :
  env -> Prims.string Prims.list -> env FStar_Tactics_Monad.tac) =
  fun uu___1 ->
    fun uu___ ->
      (fun e ->
         fun ns ->
           let lid =
             FStar_Ident.lid_of_path ns FStar_Compiler_Range_Type.dummyRange in
           let uu___ =
             let uu___1 =
               FStar_Syntax_DsEnv.push_namespace
                 e.FStar_TypeChecker_Env.dsenv lid in
             {
               FStar_TypeChecker_Env.solver =
                 (e.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range = (e.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (e.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma = (e.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (e.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (e.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (e.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (e.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (e.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (e.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (e.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (e.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (e.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (e.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (e.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (e.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq_strict =
                 (e.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (e.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit = (e.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax = (e.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (e.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (e.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (e.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (e.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (e.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.intactics =
                 (e.FStar_TypeChecker_Env.intactics);
               FStar_TypeChecker_Env.nocoerce =
                 (e.FStar_TypeChecker_Env.nocoerce);
               FStar_TypeChecker_Env.tc_term =
                 (e.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                 (e.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
               FStar_TypeChecker_Env.universe_of =
                 (e.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                 (e.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
               FStar_TypeChecker_Env.teq_nosmt_force =
                 (e.FStar_TypeChecker_Env.teq_nosmt_force);
               FStar_TypeChecker_Env.subtype_nosmt_force =
                 (e.FStar_TypeChecker_Env.subtype_nosmt_force);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (e.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (e.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (e.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (e.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (e.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (e.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (e.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (e.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (e.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (e.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (e.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = uu___1;
               FStar_TypeChecker_Env.nbe = (e.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (e.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (e.FStar_TypeChecker_Env.erasable_types_tab);
               FStar_TypeChecker_Env.enable_defer_to_tac =
                 (e.FStar_TypeChecker_Env.enable_defer_to_tac);
               FStar_TypeChecker_Env.unif_allow_ref_guards =
                 (e.FStar_TypeChecker_Env.unif_allow_ref_guards);
               FStar_TypeChecker_Env.erase_erasable_args =
                 (e.FStar_TypeChecker_Env.erase_erasable_args);
               FStar_TypeChecker_Env.core_check =
                 (e.FStar_TypeChecker_Env.core_check)
             } in
           Obj.magic
             (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                (Obj.magic uu___))) uu___1 uu___
let (push_module_abbrev :
  env ->
    Prims.string -> Prims.string Prims.list -> env FStar_Tactics_Monad.tac)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun e ->
           fun n ->
             fun m ->
               let mlid =
                 FStar_Ident.lid_of_path m
                   FStar_Compiler_Range_Type.dummyRange in
               let ident = FStar_Ident.id_of_text n in
               let uu___ =
                 let uu___1 =
                   FStar_Syntax_DsEnv.push_module_abbrev
                     e.FStar_TypeChecker_Env.dsenv ident mlid in
                 {
                   FStar_TypeChecker_Env.solver =
                     (e.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (e.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (e.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (e.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (e.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (e.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (e.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (e.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (e.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (e.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (e.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (e.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (e.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (e.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (e.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (e.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (e.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (e.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (e.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = (e.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (e.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (e.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (e.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (e.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (e.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.intactics =
                     (e.FStar_TypeChecker_Env.intactics);
                   FStar_TypeChecker_Env.nocoerce =
                     (e.FStar_TypeChecker_Env.nocoerce);
                   FStar_TypeChecker_Env.tc_term =
                     (e.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                     (e.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                   FStar_TypeChecker_Env.universe_of =
                     (e.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                     (e.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                   FStar_TypeChecker_Env.teq_nosmt_force =
                     (e.FStar_TypeChecker_Env.teq_nosmt_force);
                   FStar_TypeChecker_Env.subtype_nosmt_force =
                     (e.FStar_TypeChecker_Env.subtype_nosmt_force);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (e.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (e.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (e.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (e.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (e.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (e.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (e.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (e.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (e.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (e.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (e.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv = uu___1;
                   FStar_TypeChecker_Env.nbe = (e.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (e.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (e.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (e.FStar_TypeChecker_Env.enable_defer_to_tac);
                   FStar_TypeChecker_Env.unif_allow_ref_guards =
                     (e.FStar_TypeChecker_Env.unif_allow_ref_guards);
                   FStar_TypeChecker_Env.erase_erasable_args =
                     (e.FStar_TypeChecker_Env.erase_erasable_args);
                   FStar_TypeChecker_Env.core_check =
                     (e.FStar_TypeChecker_Env.core_check)
                 } in
               Obj.magic
                 (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                    (Obj.magic uu___))) uu___2 uu___1 uu___
let (resolve_name :
  env ->
    Prims.string Prims.list ->
      (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv)
        FStar_Pervasives.either FStar_Pervasives_Native.option
        FStar_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun e ->
         fun n ->
           let l =
             FStar_Ident.lid_of_path n FStar_Compiler_Range_Type.dummyRange in
           let uu___ =
             FStar_Syntax_DsEnv.resolve_name e.FStar_TypeChecker_Env.dsenv l in
           Obj.magic
             (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                (Obj.magic uu___))) uu___1 uu___
let (log_issues :
  FStar_Errors.issue Prims.list -> unit FStar_Tactics_Monad.tac) =
  fun is ->
    FStar_Class_Monad.op_let_Bang FStar_Tactics_Monad.monad_tac () ()
      (Obj.magic FStar_Tactics_Monad.get)
      (fun uu___ ->
         (fun ps ->
            let ps = Obj.magic ps in
            let is1 =
              FStar_Compiler_List.map
                (fun i ->
                   let uu___ =
                     let uu___1 =
                       FStar_Errors_Msg.text "Tactic logged issue:" in
                     uu___1 :: (i.FStar_Errors.issue_msg) in
                   {
                     FStar_Errors.issue_msg = uu___;
                     FStar_Errors.issue_level = (i.FStar_Errors.issue_level);
                     FStar_Errors.issue_range = (i.FStar_Errors.issue_range);
                     FStar_Errors.issue_number =
                       (i.FStar_Errors.issue_number);
                     FStar_Errors.issue_ctx = (i.FStar_Errors.issue_ctx)
                   }) is in
            FStar_Errors.add_issues is1;
            Obj.magic
              (FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac ()
                 (Obj.repr ()))) uu___)
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env1 ->
    let uu___ = FStar_TypeChecker_Env.clear_expected_typ env1 in
    match uu___ with
    | (env2, uu___1) ->
        let env3 =
          {
            FStar_TypeChecker_Env.solver =
              (env2.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range = (env2.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (env2.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma = (env2.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (env2.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (env2.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (env2.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (env2.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (env2.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (env2.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (env2.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (env2.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (env2.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (env2.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (env2.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq_strict =
              (env2.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (env2.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit = (env2.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = (env2.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (env2.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (env2.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (env2.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (env2.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (env2.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.intactics =
              (env2.FStar_TypeChecker_Env.intactics);
            FStar_TypeChecker_Env.nocoerce =
              (env2.FStar_TypeChecker_Env.nocoerce);
            FStar_TypeChecker_Env.tc_term =
              (env2.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
              (env2.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
            FStar_TypeChecker_Env.universe_of =
              (env2.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
              (env2.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
            FStar_TypeChecker_Env.teq_nosmt_force =
              (env2.FStar_TypeChecker_Env.teq_nosmt_force);
            FStar_TypeChecker_Env.subtype_nosmt_force =
              (env2.FStar_TypeChecker_Env.subtype_nosmt_force);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (env2.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (env2.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (env2.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (env2.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (env2.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (env2.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (env2.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (env2.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (env2.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (env2.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (env2.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv = (env2.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe = (env2.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (env2.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (env2.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (env2.FStar_TypeChecker_Env.enable_defer_to_tac);
            FStar_TypeChecker_Env.unif_allow_ref_guards =
              (env2.FStar_TypeChecker_Env.unif_allow_ref_guards);
            FStar_TypeChecker_Env.erase_erasable_args =
              (env2.FStar_TypeChecker_Env.erase_erasable_args);
            FStar_TypeChecker_Env.core_check =
              (env2.FStar_TypeChecker_Env.core_check)
          } in
        let env4 =
          {
            FStar_TypeChecker_Env.solver =
              (env3.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range = (env3.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (env3.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma = (env3.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (env3.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (env3.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (env3.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (env3.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (env3.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (env3.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (env3.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (env3.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (env3.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (env3.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (env3.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (env3.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq_strict =
              (env3.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (env3.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit = (env3.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = (env3.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (env3.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (env3.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (env3.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (env3.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.intactics =
              (env3.FStar_TypeChecker_Env.intactics);
            FStar_TypeChecker_Env.nocoerce =
              (env3.FStar_TypeChecker_Env.nocoerce);
            FStar_TypeChecker_Env.tc_term =
              (env3.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
              (env3.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
            FStar_TypeChecker_Env.universe_of =
              (env3.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
              (env3.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
            FStar_TypeChecker_Env.teq_nosmt_force =
              (env3.FStar_TypeChecker_Env.teq_nosmt_force);
            FStar_TypeChecker_Env.subtype_nosmt_force =
              (env3.FStar_TypeChecker_Env.subtype_nosmt_force);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (env3.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (env3.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (env3.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (env3.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (env3.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (env3.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (env3.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (env3.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (env3.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (env3.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (env3.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv = (env3.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe = (env3.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (env3.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (env3.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (env3.FStar_TypeChecker_Env.enable_defer_to_tac);
            FStar_TypeChecker_Env.unif_allow_ref_guards =
              (env3.FStar_TypeChecker_Env.unif_allow_ref_guards);
            FStar_TypeChecker_Env.erase_erasable_args =
              (env3.FStar_TypeChecker_Env.erase_erasable_args);
            FStar_TypeChecker_Env.core_check =
              (env3.FStar_TypeChecker_Env.core_check)
          } in
        let env5 =
          {
            FStar_TypeChecker_Env.solver =
              (env4.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range = (env4.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (env4.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma = (env4.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (env4.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (env4.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (env4.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (env4.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (env4.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (env4.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (env4.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (env4.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (env4.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (env4.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (env4.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (env4.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq_strict =
              (env4.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (env4.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit = (env4.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = (env4.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (env4.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (env4.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (env4.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (env4.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (env4.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.intactics =
              (env4.FStar_TypeChecker_Env.intactics);
            FStar_TypeChecker_Env.nocoerce =
              (env4.FStar_TypeChecker_Env.nocoerce);
            FStar_TypeChecker_Env.tc_term =
              (env4.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
              (env4.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
            FStar_TypeChecker_Env.universe_of =
              (env4.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
              (env4.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
            FStar_TypeChecker_Env.teq_nosmt_force =
              (env4.FStar_TypeChecker_Env.teq_nosmt_force);
            FStar_TypeChecker_Env.subtype_nosmt_force =
              (env4.FStar_TypeChecker_Env.subtype_nosmt_force);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (env4.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (env4.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (env4.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (env4.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (env4.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (env4.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (env4.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (env4.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (env4.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (env4.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (env4.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv = (env4.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe = (env4.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (env4.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (env4.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac = false;
            FStar_TypeChecker_Env.unif_allow_ref_guards =
              (env4.FStar_TypeChecker_Env.unif_allow_ref_guards);
            FStar_TypeChecker_Env.erase_erasable_args =
              (env4.FStar_TypeChecker_Env.erase_erasable_args);
            FStar_TypeChecker_Env.core_check =
              (env4.FStar_TypeChecker_Env.core_check)
          } in
        env5
let (proofstate_of_goals :
  FStar_Compiler_Range_Type.range ->
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
            let uu___ =
              FStar_TypeChecker_Env.debug env2
                (FStar_Options.Other "TacVerbose") in
            let uu___1 = FStar_Compiler_Util.psmap_empty () in
            {
              FStar_Tactics_Types.main_context = env2;
              FStar_Tactics_Types.all_implicits = imps;
              FStar_Tactics_Types.goals = goals;
              FStar_Tactics_Types.smt_goals = [];
              FStar_Tactics_Types.depth = Prims.int_zero;
              FStar_Tactics_Types.__dump =
                FStar_Tactics_Printing.do_dump_proofstate;
              FStar_Tactics_Types.psc =
                FStar_TypeChecker_Primops_Base.null_psc;
              FStar_Tactics_Types.entry_range = rng;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
              FStar_Tactics_Types.freshness = Prims.int_zero;
              FStar_Tactics_Types.tac_verb_dbg = uu___;
              FStar_Tactics_Types.local_state = uu___1;
              FStar_Tactics_Types.urgency = Prims.int_one
            } in
          ps
let (proofstate_of_goal_ty :
  FStar_Compiler_Range_Type.range ->
    env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env1 ->
      fun typ ->
        let env2 =
          {
            FStar_TypeChecker_Env.solver =
              (env1.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range = rng;
            FStar_TypeChecker_Env.curmodule =
              (env1.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma = (env1.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (env1.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (env1.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (env1.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (env1.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (env1.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (env1.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (env1.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (env1.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (env1.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (env1.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (env1.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (env1.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq_strict =
              (env1.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (env1.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit = (env1.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = (env1.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (env1.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (env1.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (env1.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (env1.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (env1.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.intactics =
              (env1.FStar_TypeChecker_Env.intactics);
            FStar_TypeChecker_Env.nocoerce =
              (env1.FStar_TypeChecker_Env.nocoerce);
            FStar_TypeChecker_Env.tc_term =
              (env1.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
              (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
            FStar_TypeChecker_Env.universe_of =
              (env1.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
              (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
            FStar_TypeChecker_Env.teq_nosmt_force =
              (env1.FStar_TypeChecker_Env.teq_nosmt_force);
            FStar_TypeChecker_Env.subtype_nosmt_force =
              (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (env1.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (env1.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (env1.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (env1.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (env1.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (env1.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (env1.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (env1.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (env1.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv = (env1.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe = (env1.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (env1.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (env1.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
            FStar_TypeChecker_Env.unif_allow_ref_guards =
              (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
            FStar_TypeChecker_Env.erase_erasable_args =
              (env1.FStar_TypeChecker_Env.erase_erasable_args);
            FStar_TypeChecker_Env.core_check =
              (env1.FStar_TypeChecker_Env.core_check)
          } in
        let env3 = tac_env env2 in
        let uu___ = FStar_Tactics_Types.goal_of_goal_ty env3 typ in
        match uu___ with
        | (g, g_u) ->
            let ps =
              proofstate_of_goals rng env3 [g]
                g_u.FStar_TypeChecker_Common.implicits in
            let uu___1 = FStar_Tactics_Types.goal_witness g in (ps, uu___1)
let (proofstate_of_all_implicits :
  FStar_Compiler_Range_Type.range ->
    env ->
      implicits ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env1 ->
      fun imps ->
        let env2 = tac_env env1 in
        let goals =
          FStar_Compiler_List.map (FStar_Tactics_Types.goal_of_implicit env2)
            imps in
        let w =
          let uu___ = FStar_Compiler_List.hd goals in
          FStar_Tactics_Types.goal_witness uu___ in
        let ps =
          let uu___ =
            FStar_TypeChecker_Env.debug env2
              (FStar_Options.Other "TacVerbose") in
          let uu___1 = FStar_Compiler_Util.psmap_empty () in
          {
            FStar_Tactics_Types.main_context = env2;
            FStar_Tactics_Types.all_implicits = imps;
            FStar_Tactics_Types.goals = goals;
            FStar_Tactics_Types.smt_goals = [];
            FStar_Tactics_Types.depth = Prims.int_zero;
            FStar_Tactics_Types.__dump =
              FStar_Tactics_Printing.do_dump_proofstate;
            FStar_Tactics_Types.psc = FStar_TypeChecker_Primops_Base.null_psc;
            FStar_Tactics_Types.entry_range = rng;
            FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
            FStar_Tactics_Types.freshness = Prims.int_zero;
            FStar_Tactics_Types.tac_verb_dbg = uu___;
            FStar_Tactics_Types.local_state = uu___1;
            FStar_Tactics_Types.urgency = Prims.int_one
          } in
        (ps, w)
let (getprop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e ->
    fun t ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant] e t in
      FStar_Syntax_Util.un_squash tn
let run_unembedded_tactic_on_ps_and_solve_remaining :
  'a 'b .
    FStar_Compiler_Range_Type.range ->
      FStar_Compiler_Range_Type.range ->
        Prims.bool ->
          'a ->
            ('a -> 'b FStar_Tactics_Monad.tac) ->
              FStar_Tactics_Types.proofstate -> 'b
  =
  fun t_range ->
    fun g_range ->
      fun background ->
        fun t ->
          fun f ->
            fun ps ->
              let uu___ =
                FStar_Tactics_Interpreter.run_unembedded_tactic_on_ps t_range
                  g_range background t f ps in
              match uu___ with
              | (remaining_goals, r) ->
                  (FStar_Compiler_List.iter
                     (fun g ->
                        let uu___2 =
                          let uu___3 = FStar_Tactics_Types.goal_env g in
                          let uu___4 = FStar_Tactics_Types.goal_type g in
                          getprop uu___3 uu___4 in
                        match uu___2 with
                        | FStar_Pervasives_Native.Some vc ->
                            let guard =
                              {
                                FStar_TypeChecker_Common.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Common.deferred_to_tac = [];
                                FStar_TypeChecker_Common.deferred = [];
                                FStar_TypeChecker_Common.univ_ineqs =
                                  ([], []);
                                FStar_TypeChecker_Common.implicits = []
                              } in
                            let uu___3 = FStar_Tactics_Types.goal_env g in
                            FStar_TypeChecker_Rel.force_trivial_guard uu___3
                              guard
                        | FStar_Pervasives_Native.None ->
                            FStar_Errors.raise_error
                              (FStar_Errors_Codes.Fatal_OpenGoalsInSynthesis,
                                "tactic left a computationally-relevant goal unsolved")
                              g_range) remaining_goals;
                   r)
let (call_subtac :
  env ->
    unit FStar_Tactics_Monad.tac ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * issues)
            FStar_Tactics_Monad.tac)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun f ->
               fun _u ->
                 fun goal_ty ->
                   let uu___ =
                     FStar_Class_Monad.return FStar_Tactics_Monad.monad_tac
                       () (Obj.repr ()) in
                   Obj.magic
                     (FStar_Class_Monad.op_let_Bang
                        FStar_Tactics_Monad.monad_tac () () uu___
                        (fun uu___1 ->
                           (fun uu___1 ->
                              let uu___1 = Obj.magic uu___1 in
                              let rng = FStar_TypeChecker_Env.get_range g in
                              let uu___2 =
                                proofstate_of_goal_ty rng g goal_ty in
                              match uu___2 with
                              | (ps, w) ->
                                  let uu___3 =
                                    FStar_Errors.catch_errors_and_ignore_rest
                                      (fun uu___4 ->
                                         run_unembedded_tactic_on_ps_and_solve_remaining
                                           rng rng false () (fun uu___5 -> f)
                                           ps) in
                                  (match uu___3 with
                                   | ([], FStar_Pervasives_Native.Some ()) ->
                                       Obj.magic
                                         (FStar_Class_Monad.return
                                            FStar_Tactics_Monad.monad_tac ()
                                            (Obj.magic
                                               ((FStar_Pervasives_Native.Some
                                                   w), [])))
                                   | (issues1, uu___4) ->
                                       Obj.magic
                                         (FStar_Class_Monad.return
                                            FStar_Tactics_Monad.monad_tac ()
                                            (Obj.magic
                                               (FStar_Pervasives_Native.None,
                                                 issues1))))) uu___1)))
            uu___3 uu___2 uu___1 uu___