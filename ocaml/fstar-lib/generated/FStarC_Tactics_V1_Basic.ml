open Prims
let (dbg_2635 : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "2635"
let (dbg_ReflTc : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "ReflTc"
let (dbg_Tac : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Tac"
let (dbg_TacUnify : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "TacUnify"
let ret : 'a . 'a -> 'a FStarC_Tactics_Monad.tac =
  fun uu___ ->
    (fun x ->
       Obj.magic
         (FStarC_Class_Monad.return FStarC_Tactics_Monad.monad_tac ()
            (Obj.magic x))) uu___
let bind :
  'a 'b .
    unit ->
      'a FStarC_Tactics_Monad.tac ->
        ('a -> 'b FStarC_Tactics_Monad.tac) -> 'b FStarC_Tactics_Monad.tac
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun uu___ ->
           Obj.magic
             (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac
                () ())) uu___2 uu___1 uu___
let (idtac : unit FStarC_Tactics_Monad.tac) =
  FStarC_Class_Monad.return FStarC_Tactics_Monad.monad_tac () (Obj.repr ())
let (get_phi :
  FStarC_Tactics_Types.goal ->
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g ->
    let uu___ =
      let uu___1 = FStarC_Tactics_Types.goal_env g in
      let uu___2 = FStarC_Tactics_Types.goal_type g in
      FStarC_TypeChecker_Normalize.unfold_whnf uu___1 uu___2 in
    FStarC_Syntax_Util.un_squash uu___
let (is_irrelevant : FStarC_Tactics_Types.goal -> Prims.bool) =
  fun g -> let uu___ = get_phi g in FStarC_Compiler_Option.isSome uu___
let (core_check :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.typ ->
        Prims.bool ->
          (FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option,
            FStarC_TypeChecker_Core.error) FStar_Pervasives.either)
  =
  fun env ->
    fun sol ->
      fun t ->
        fun must_tot ->
          let uu___ =
            let uu___1 = FStarC_Options.compat_pre_core_should_check () in
            Prims.op_Negation uu___1 in
          if uu___
          then FStar_Pervasives.Inl FStar_Pervasives_Native.None
          else
            (let debug f =
               let uu___2 = FStarC_Compiler_Debug.any () in
               if uu___2 then f () else () in
             let uu___2 =
               FStarC_TypeChecker_Core.check_term env sol t must_tot in
             match uu___2 with
             | FStar_Pervasives.Inl (FStar_Pervasives_Native.None) ->
                 FStar_Pervasives.Inl FStar_Pervasives_Native.None
             | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g) ->
                 let uu___3 = FStarC_Options.compat_pre_core_set () in
                 if uu___3
                 then FStar_Pervasives.Inl FStar_Pervasives_Native.None
                 else FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g)
             | FStar_Pervasives.Inr err ->
                 (debug
                    (fun uu___4 ->
                       let uu___5 =
                         let uu___6 = FStarC_TypeChecker_Env.get_range env in
                         FStarC_Class_Show.show
                           FStarC_Compiler_Range_Ops.showable_range uu___6 in
                       let uu___6 =
                         FStarC_TypeChecker_Core.print_error_short err in
                       let uu___7 =
                         FStarC_Class_Show.show
                           FStarC_Syntax_Print.showable_term sol in
                       let uu___8 =
                         FStarC_Class_Show.show
                           FStarC_Syntax_Print.showable_term t in
                       let uu___9 = FStarC_TypeChecker_Core.print_error err in
                       FStarC_Compiler_Util.print5
                         "(%s) Core checking failed (%s) on term %s and type %s\n%s\n"
                         uu___5 uu___6 uu___7 uu___8 uu___9);
                  FStar_Pervasives.Inr err))
type name = FStarC_Syntax_Syntax.bv
type env = FStarC_TypeChecker_Env.env
type implicits = FStarC_TypeChecker_Env.implicits
let (rangeof : FStarC_Tactics_Types.goal -> FStarC_Compiler_Range_Type.range)
  =
  fun g ->
    (g.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_range
let (normalize :
  FStarC_TypeChecker_Env.steps ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  = fun s -> fun e -> fun t -> FStarC_TypeChecker_Normalize.normalize s e t
let (bnorm :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  = fun e -> fun t -> normalize [] e t
let (whnf :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  = fun e -> fun t -> FStarC_TypeChecker_Normalize.unfold_whnf e t
let (tts :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> Prims.string) =
  FStarC_TypeChecker_Normalize.term_to_string
let (set_uvar_expected_typ :
  FStarC_Syntax_Syntax.ctx_uvar -> FStarC_Syntax_Syntax.typ -> unit) =
  fun u ->
    fun t ->
      let dec =
        FStarC_Syntax_Unionfind.find_decoration
          u.FStarC_Syntax_Syntax.ctx_uvar_head in
      FStarC_Syntax_Unionfind.change_decoration
        u.FStarC_Syntax_Syntax.ctx_uvar_head
        {
          FStarC_Syntax_Syntax.uvar_decoration_typ = t;
          FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on =
            (dec.FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on);
          FStarC_Syntax_Syntax.uvar_decoration_should_check =
            (dec.FStarC_Syntax_Syntax.uvar_decoration_should_check);
          FStarC_Syntax_Syntax.uvar_decoration_should_unrefine =
            (dec.FStarC_Syntax_Syntax.uvar_decoration_should_unrefine)
        }
let (mark_uvar_with_should_check_tag :
  FStarC_Syntax_Syntax.ctx_uvar ->
    FStarC_Syntax_Syntax.should_check_uvar -> unit)
  =
  fun u ->
    fun sc ->
      let dec =
        FStarC_Syntax_Unionfind.find_decoration
          u.FStarC_Syntax_Syntax.ctx_uvar_head in
      FStarC_Syntax_Unionfind.change_decoration
        u.FStarC_Syntax_Syntax.ctx_uvar_head
        {
          FStarC_Syntax_Syntax.uvar_decoration_typ =
            (dec.FStarC_Syntax_Syntax.uvar_decoration_typ);
          FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on =
            (dec.FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on);
          FStarC_Syntax_Syntax.uvar_decoration_should_check = sc;
          FStarC_Syntax_Syntax.uvar_decoration_should_unrefine =
            (dec.FStarC_Syntax_Syntax.uvar_decoration_should_unrefine)
        }
let (mark_uvar_as_already_checked : FStarC_Syntax_Syntax.ctx_uvar -> unit) =
  fun u ->
    mark_uvar_with_should_check_tag u FStarC_Syntax_Syntax.Already_checked
let (mark_goal_implicit_already_checked : FStarC_Tactics_Types.goal -> unit)
  =
  fun g -> mark_uvar_as_already_checked g.FStarC_Tactics_Types.goal_ctx_uvar
let (goal_with_type :
  FStarC_Tactics_Types.goal ->
    FStarC_Syntax_Syntax.typ -> FStarC_Tactics_Types.goal)
  =
  fun g ->
    fun t ->
      let u = g.FStarC_Tactics_Types.goal_ctx_uvar in
      set_uvar_expected_typ u t; g
let (bnorm_goal : FStarC_Tactics_Types.goal -> FStarC_Tactics_Types.goal) =
  fun g ->
    let uu___ =
      let uu___1 = FStarC_Tactics_Types.goal_env g in
      let uu___2 = FStarC_Tactics_Types.goal_type g in bnorm uu___1 uu___2 in
    goal_with_type g uu___
let (tacprint : Prims.string -> unit) =
  fun s -> FStarC_Compiler_Util.print1 "TAC>> %s\n" s
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      let uu___ = FStarC_Compiler_Util.format1 s x in
      FStarC_Compiler_Util.print1 "TAC>> %s\n" uu___
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        let uu___ = FStarC_Compiler_Util.format2 s x y in
        FStarC_Compiler_Util.print1 "TAC>> %s\n" uu___
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        fun z ->
          let uu___ = FStarC_Compiler_Util.format3 s x y z in
          FStarC_Compiler_Util.print1 "TAC>> %s\n" uu___
let (print : Prims.string -> unit FStarC_Tactics_Monad.tac) =
  fun msg ->
    (let uu___1 =
       (let uu___2 = FStarC_Options.silent () in Prims.op_Negation uu___2) ||
         (FStarC_Options.interactive ()) in
     if uu___1 then tacprint msg else ());
    ret ()
let (debugging : unit -> Prims.bool FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 = bind () in
    uu___1 FStarC_Tactics_Monad.get
      (fun ps ->
         let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_Tac in ret uu___2)
let (do_dump_ps : Prims.string -> FStarC_Tactics_Types.proofstate -> unit) =
  fun msg ->
    fun ps ->
      let psc = ps.FStarC_Tactics_Types.psc in
      let subst = FStarC_TypeChecker_Primops_Base.psc_subst psc in
      FStarC_Tactics_Printing.do_dump_proofstate ps msg
let (dump : Prims.string -> unit FStarC_Tactics_Monad.tac) =
  fun msg ->
    FStarC_Tactics_Monad.mk_tac
      (fun ps -> do_dump_ps msg ps; FStarC_Tactics_Result.Success ((), ps))
let (dump_all : Prims.bool -> Prims.string -> unit FStarC_Tactics_Monad.tac)
  =
  fun print_resolved ->
    fun msg ->
      FStarC_Tactics_Monad.mk_tac
        (fun ps ->
           let gs =
             FStarC_Compiler_List.map
               (fun i ->
                  FStarC_Tactics_Types.goal_of_implicit
                    ps.FStarC_Tactics_Types.main_context i)
               ps.FStarC_Tactics_Types.all_implicits in
           let gs1 =
             if print_resolved
             then gs
             else
               FStarC_Compiler_List.filter
                 (fun g ->
                    let uu___1 = FStarC_Tactics_Types.check_goal_solved g in
                    Prims.op_Negation uu___1) gs in
           let ps' =
             {
               FStarC_Tactics_Types.main_context =
                 (ps.FStarC_Tactics_Types.main_context);
               FStarC_Tactics_Types.all_implicits =
                 (ps.FStarC_Tactics_Types.all_implicits);
               FStarC_Tactics_Types.goals = gs1;
               FStarC_Tactics_Types.smt_goals = [];
               FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
               FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
               FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
               FStarC_Tactics_Types.entry_range =
                 (ps.FStarC_Tactics_Types.entry_range);
               FStarC_Tactics_Types.guard_policy =
                 (ps.FStarC_Tactics_Types.guard_policy);
               FStarC_Tactics_Types.freshness =
                 (ps.FStarC_Tactics_Types.freshness);
               FStarC_Tactics_Types.tac_verb_dbg =
                 (ps.FStarC_Tactics_Types.tac_verb_dbg);
               FStarC_Tactics_Types.local_state =
                 (ps.FStarC_Tactics_Types.local_state);
               FStarC_Tactics_Types.urgency =
                 (ps.FStarC_Tactics_Types.urgency);
               FStarC_Tactics_Types.dump_on_failure =
                 (ps.FStarC_Tactics_Types.dump_on_failure)
             } in
           do_dump_ps msg ps'; FStarC_Tactics_Result.Success ((), ps))
let (dump_uvars_of :
  FStarC_Tactics_Types.goal -> Prims.string -> unit FStarC_Tactics_Monad.tac)
  =
  fun g ->
    fun msg ->
      FStarC_Tactics_Monad.mk_tac
        (fun ps ->
           let uvs =
             let uu___ =
               let uu___1 = FStarC_Tactics_Types.goal_type g in
               FStarC_Syntax_Free.uvars uu___1 in
             FStarC_Class_Setlike.elems ()
               (Obj.magic
                  (FStarC_Compiler_FlatSet.setlike_flat_set
                     FStarC_Syntax_Free.ord_ctx_uvar)) (Obj.magic uu___) in
           let gs =
             FStarC_Compiler_List.map
               (FStarC_Tactics_Types.goal_of_ctx_uvar g) uvs in
           let gs1 =
             FStarC_Compiler_List.filter
               (fun g1 ->
                  let uu___ = FStarC_Tactics_Types.check_goal_solved g1 in
                  Prims.op_Negation uu___) gs in
           let ps' =
             {
               FStarC_Tactics_Types.main_context =
                 (ps.FStarC_Tactics_Types.main_context);
               FStarC_Tactics_Types.all_implicits =
                 (ps.FStarC_Tactics_Types.all_implicits);
               FStarC_Tactics_Types.goals = gs1;
               FStarC_Tactics_Types.smt_goals = [];
               FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
               FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
               FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
               FStarC_Tactics_Types.entry_range =
                 (ps.FStarC_Tactics_Types.entry_range);
               FStarC_Tactics_Types.guard_policy =
                 (ps.FStarC_Tactics_Types.guard_policy);
               FStarC_Tactics_Types.freshness =
                 (ps.FStarC_Tactics_Types.freshness);
               FStarC_Tactics_Types.tac_verb_dbg =
                 (ps.FStarC_Tactics_Types.tac_verb_dbg);
               FStarC_Tactics_Types.local_state =
                 (ps.FStarC_Tactics_Types.local_state);
               FStarC_Tactics_Types.urgency =
                 (ps.FStarC_Tactics_Types.urgency);
               FStarC_Tactics_Types.dump_on_failure =
                 (ps.FStarC_Tactics_Types.dump_on_failure)
             } in
           do_dump_ps msg ps'; FStarC_Tactics_Result.Success ((), ps))
let fail1 :
  'uuuuu . Prims.string -> Prims.string -> 'uuuuu FStarC_Tactics_Monad.tac =
  fun msg ->
    fun x ->
      let uu___ = FStarC_Compiler_Util.format1 msg x in
      FStarC_Tactics_Monad.fail uu___
let fail2 :
  'uuuuu .
    Prims.string ->
      Prims.string -> Prims.string -> 'uuuuu FStarC_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        let uu___ = FStarC_Compiler_Util.format2 msg x y in
        FStarC_Tactics_Monad.fail uu___
let fail3 :
  'uuuuu .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> 'uuuuu FStarC_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          let uu___ = FStarC_Compiler_Util.format3 msg x y z in
          FStarC_Tactics_Monad.fail uu___
let fail4 :
  'uuuuu .
    Prims.string ->
      Prims.string ->
        Prims.string ->
          Prims.string -> Prims.string -> 'uuuuu FStarC_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          fun w ->
            let uu___ = FStarC_Compiler_Util.format4 msg x y z w in
            FStarC_Tactics_Monad.fail uu___
let (destruct_eq' :
  FStarC_Syntax_Syntax.typ ->
    (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu___ = FStarC_Syntax_Formula.destruct_typ_as_formula typ in
    match uu___ with
    | FStar_Pervasives_Native.Some (FStarC_Syntax_Formula.BaseConn
        (l,
         uu___1::(e1, FStar_Pervasives_Native.None)::(e2,
                                                      FStar_Pervasives_Native.None)::[]))
        when
        (FStarC_Ident.lid_equals l FStarC_Parser_Const.eq2_lid) ||
          (FStarC_Ident.lid_equals l FStarC_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu___1 ->
        let uu___2 = FStarC_Syntax_Util.unb2t typ in
        (match uu___2 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu___3 = FStarC_Syntax_Util.head_and_args t in
             (match uu___3 with
              | (hd, args) ->
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStarC_Syntax_Subst.compress hd in
                      uu___6.FStarC_Syntax_Syntax.n in
                    (uu___5, args) in
                  (match uu___4 with
                   | (FStarC_Syntax_Syntax.Tm_fvar fv,
                      (uu___5, FStar_Pervasives_Native.Some
                       { FStarC_Syntax_Syntax.aqual_implicit = true;
                         FStarC_Syntax_Syntax.aqual_attributes = uu___6;_})::
                      (e1, FStar_Pervasives_Native.None)::(e2,
                                                           FStar_Pervasives_Native.None)::[])
                       when
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu___5 -> FStar_Pervasives_Native.None)))
let (destruct_eq :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ ->
      (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun typ ->
      let typ1 = whnf env1 typ in
      let uu___ = destruct_eq' typ1 in
      match uu___ with
      | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
      | FStar_Pervasives_Native.None ->
          let uu___1 = FStarC_Syntax_Util.un_squash typ1 in
          (match uu___1 with
           | FStar_Pervasives_Native.Some typ2 ->
               let typ3 = whnf env1 typ2 in destruct_eq' typ3
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (get_guard_policy :
  unit -> FStarC_Tactics_Types.guard_policy FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 = bind () in
    uu___1 FStarC_Tactics_Monad.get
      (fun ps -> ret ps.FStarC_Tactics_Types.guard_policy)
let (set_guard_policy :
  FStarC_Tactics_Types.guard_policy -> unit FStarC_Tactics_Monad.tac) =
  fun pol ->
    let uu___ = bind () in
    uu___ FStarC_Tactics_Monad.get
      (fun ps ->
         FStarC_Tactics_Monad.set
           {
             FStarC_Tactics_Types.main_context =
               (ps.FStarC_Tactics_Types.main_context);
             FStarC_Tactics_Types.all_implicits =
               (ps.FStarC_Tactics_Types.all_implicits);
             FStarC_Tactics_Types.goals = (ps.FStarC_Tactics_Types.goals);
             FStarC_Tactics_Types.smt_goals =
               (ps.FStarC_Tactics_Types.smt_goals);
             FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
             FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
             FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
             FStarC_Tactics_Types.entry_range =
               (ps.FStarC_Tactics_Types.entry_range);
             FStarC_Tactics_Types.guard_policy = pol;
             FStarC_Tactics_Types.freshness =
               (ps.FStarC_Tactics_Types.freshness);
             FStarC_Tactics_Types.tac_verb_dbg =
               (ps.FStarC_Tactics_Types.tac_verb_dbg);
             FStarC_Tactics_Types.local_state =
               (ps.FStarC_Tactics_Types.local_state);
             FStarC_Tactics_Types.urgency = (ps.FStarC_Tactics_Types.urgency);
             FStarC_Tactics_Types.dump_on_failure =
               (ps.FStarC_Tactics_Types.dump_on_failure)
           })
let with_policy :
  'a .
    FStarC_Tactics_Types.guard_policy ->
      'a FStarC_Tactics_Monad.tac -> 'a FStarC_Tactics_Monad.tac
  =
  fun pol ->
    fun t ->
      let uu___ = get_guard_policy () in
      let uu___1 = bind () in
      uu___1 uu___
        (fun old_pol ->
           let uu___2 = set_guard_policy pol in
           let uu___3 = bind () in
           uu___3 uu___2
             (fun uu___4 ->
                let uu___5 = bind () in
                uu___5 t
                  (fun r ->
                     let uu___6 = set_guard_policy old_pol in
                     let uu___7 = bind () in
                     uu___7 uu___6 (fun uu___8 -> ret r))))
let (proc_guard' :
  Prims.bool ->
    Prims.string ->
      env ->
        FStarC_TypeChecker_Common.guard_t ->
          FStarC_Syntax_Syntax.should_check_uvar
            FStar_Pervasives_Native.option ->
            FStarC_Compiler_Range_Type.range -> unit FStarC_Tactics_Monad.tac)
  =
  fun simplify ->
    fun reason ->
      fun e ->
        fun g ->
          fun sc_opt ->
            fun rng ->
              FStarC_Tactics_Monad.mlog
                (fun uu___ ->
                   let uu___1 = FStarC_TypeChecker_Rel.guard_to_string e g in
                   FStarC_Compiler_Util.print2 "Processing guard (%s:%s)\n"
                     reason uu___1)
                (fun uu___ ->
                   let imps =
                     FStarC_Class_Listlike.to_list
                       (FStarC_Compiler_CList.listlike_clist ())
                       g.FStarC_TypeChecker_Common.implicits in
                   (match sc_opt with
                    | FStar_Pervasives_Native.Some
                        (FStarC_Syntax_Syntax.Allow_untyped r) ->
                        FStarC_Compiler_List.iter
                          (fun imp ->
                             mark_uvar_with_should_check_tag
                               imp.FStarC_TypeChecker_Common.imp_uvar
                               (FStarC_Syntax_Syntax.Allow_untyped r)) imps
                    | uu___2 -> ());
                   (let uu___2 = FStarC_Tactics_Monad.add_implicits imps in
                    FStarC_Class_Monad.op_let_Bang
                      FStarC_Tactics_Monad.monad_tac () () uu___2
                      (fun uu___3 ->
                         (fun uu___3 ->
                            let uu___3 = Obj.magic uu___3 in
                            let guard_f =
                              if simplify
                              then
                                let uu___4 =
                                  FStarC_TypeChecker_Rel.simplify_guard e g in
                                uu___4.FStarC_TypeChecker_Common.guard_f
                              else g.FStarC_TypeChecker_Common.guard_f in
                            match guard_f with
                            | FStarC_TypeChecker_Common.Trivial ->
                                Obj.magic (ret ())
                            | FStarC_TypeChecker_Common.NonTrivial f ->
                                Obj.magic
                                  (FStarC_Class_Monad.op_let_Bang
                                     FStarC_Tactics_Monad.monad_tac () ()
                                     (Obj.magic FStarC_Tactics_Monad.get)
                                     (fun uu___4 ->
                                        (fun ps ->
                                           let ps = Obj.magic ps in
                                           match ps.FStarC_Tactics_Types.guard_policy
                                           with
                                           | FStarC_Tactics_Types.Drop ->
                                               ((let uu___5 =
                                                   let uu___6 =
                                                     FStarC_TypeChecker_Rel.guard_to_string
                                                       e g in
                                                   FStarC_Compiler_Util.format1
                                                     "Tactics admitted guard <%s>\n\n"
                                                     uu___6 in
                                                 FStarC_Errors.log_issue
                                                   FStarC_TypeChecker_Env.hasRange_env
                                                   e
                                                   FStarC_Errors_Codes.Warning_TacAdmit
                                                   ()
                                                   (Obj.magic
                                                      FStarC_Errors_Msg.is_error_message_string)
                                                   (Obj.magic uu___5));
                                                Obj.magic (ret ()))
                                           | FStarC_Tactics_Types.Goal ->
                                               Obj.magic
                                                 (FStarC_Tactics_Monad.mlog
                                                    (fun uu___4 ->
                                                       let uu___5 =
                                                         FStarC_TypeChecker_Rel.guard_to_string
                                                           e g in
                                                       FStarC_Compiler_Util.print2
                                                         "Making guard (%s:%s) into a goal\n"
                                                         reason uu___5)
                                                    (fun uu___4 ->
                                                       let uu___5 =
                                                         FStarC_Tactics_Monad.goal_of_guard
                                                           reason e f sc_opt
                                                           rng in
                                                       FStarC_Class_Monad.op_let_Bang
                                                         FStarC_Tactics_Monad.monad_tac
                                                         () ()
                                                         (Obj.magic uu___5)
                                                         (fun uu___6 ->
                                                            (fun g1 ->
                                                               let g1 =
                                                                 Obj.magic g1 in
                                                               Obj.magic
                                                                 (FStarC_Tactics_Monad.push_goals
                                                                    [g1]))
                                                              uu___6)))
                                           | FStarC_Tactics_Types.SMT ->
                                               Obj.magic
                                                 (FStarC_Tactics_Monad.mlog
                                                    (fun uu___4 ->
                                                       let uu___5 =
                                                         FStarC_Class_Show.show
                                                           FStarC_Syntax_Print.showable_term
                                                           f in
                                                       FStarC_Compiler_Util.print2
                                                         "Pushing guard (%s:%s) as SMT goal\n"
                                                         reason uu___5)
                                                    (fun uu___4 ->
                                                       let uu___5 =
                                                         FStarC_Tactics_Monad.goal_of_guard
                                                           reason e f sc_opt
                                                           rng in
                                                       FStarC_Class_Monad.op_let_Bang
                                                         FStarC_Tactics_Monad.monad_tac
                                                         () ()
                                                         (Obj.magic uu___5)
                                                         (fun uu___6 ->
                                                            (fun g1 ->
                                                               let g1 =
                                                                 Obj.magic g1 in
                                                               Obj.magic
                                                                 (FStarC_Tactics_Monad.push_smt_goals
                                                                    [g1]))
                                                              uu___6)))
                                           | FStarC_Tactics_Types.SMTSync ->
                                               Obj.magic
                                                 (FStarC_Tactics_Monad.mlog
                                                    (fun uu___4 ->
                                                       let uu___5 =
                                                         FStarC_Class_Show.show
                                                           FStarC_Syntax_Print.showable_term
                                                           f in
                                                       FStarC_Compiler_Util.print2
                                                         "Sending guard (%s:%s) to SMT Synchronously\n"
                                                         reason uu___5)
                                                    (fun uu___4 ->
                                                       FStarC_TypeChecker_Rel.force_trivial_guard
                                                         e g;
                                                       ret ()))
                                           | FStarC_Tactics_Types.Force ->
                                               Obj.magic
                                                 (FStarC_Tactics_Monad.mlog
                                                    (fun uu___4 ->
                                                       let uu___5 =
                                                         FStarC_TypeChecker_Rel.guard_to_string
                                                           e g in
                                                       FStarC_Compiler_Util.print2
                                                         "Forcing guard (%s:%s)\n"
                                                         reason uu___5)
                                                    (fun uu___4 ->
                                                       try
                                                         (fun uu___5 ->
                                                            match () with
                                                            | () ->
                                                                let uu___6 =
                                                                  let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    FStarC_TypeChecker_Rel.discharge_guard_no_smt
                                                                    e g in
                                                                    FStarC_TypeChecker_Env.is_trivial
                                                                    uu___8 in
                                                                  Prims.op_Negation
                                                                    uu___7 in
                                                                if uu___6
                                                                then
                                                                  FStarC_Tactics_Monad.mlog
                                                                    (
                                                                    fun
                                                                    uu___7 ->
                                                                    let uu___8
                                                                    =
                                                                    FStarC_TypeChecker_Rel.guard_to_string
                                                                    e g in
                                                                    FStarC_Compiler_Util.print1
                                                                    "guard = %s\n"
                                                                    uu___8)
                                                                    (
                                                                    fun
                                                                    uu___7 ->
                                                                    fail1
                                                                    "Forcing the guard failed (%s)"
                                                                    reason)
                                                                else ret ())
                                                           ()
                                                       with
                                                       | uu___5 ->
                                                           FStarC_Tactics_Monad.mlog
                                                             (fun uu___6 ->
                                                                let uu___7 =
                                                                  FStarC_TypeChecker_Rel.guard_to_string
                                                                    e g in
                                                                FStarC_Compiler_Util.print1
                                                                  "guard = %s\n"
                                                                  uu___7)
                                                             (fun uu___6 ->
                                                                fail1
                                                                  "Forcing the guard failed (%s)"
                                                                  reason))))
                                          uu___4))) uu___3)))
let (proc_guard :
  Prims.string ->
    env ->
      FStarC_TypeChecker_Common.guard_t ->
        FStarC_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          ->
          FStarC_Compiler_Range_Type.range -> unit FStarC_Tactics_Monad.tac)
  = proc_guard' true
let (tc_unifier_solved_implicits :
  FStarC_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStarC_Syntax_Syntax.ctx_uvar Prims.list ->
          unit FStarC_Tactics_Monad.tac)
  =
  fun env1 ->
    fun must_tot ->
      fun allow_guards ->
        fun uvs ->
          let aux u =
            let dec =
              FStarC_Syntax_Unionfind.find_decoration
                u.FStarC_Syntax_Syntax.ctx_uvar_head in
            let sc = dec.FStarC_Syntax_Syntax.uvar_decoration_should_check in
            match sc with
            | FStarC_Syntax_Syntax.Allow_untyped uu___ -> ret ()
            | FStarC_Syntax_Syntax.Already_checked -> ret ()
            | uu___ ->
                let uu___1 =
                  FStarC_Syntax_Unionfind.find
                    u.FStarC_Syntax_Syntax.ctx_uvar_head in
                (match uu___1 with
                 | FStar_Pervasives_Native.None -> ret ()
                 | FStar_Pervasives_Native.Some sol ->
                     let env2 =
                       {
                         FStarC_TypeChecker_Env.solver =
                           (env1.FStarC_TypeChecker_Env.solver);
                         FStarC_TypeChecker_Env.range =
                           (env1.FStarC_TypeChecker_Env.range);
                         FStarC_TypeChecker_Env.curmodule =
                           (env1.FStarC_TypeChecker_Env.curmodule);
                         FStarC_TypeChecker_Env.gamma =
                           (u.FStarC_Syntax_Syntax.ctx_uvar_gamma);
                         FStarC_TypeChecker_Env.gamma_sig =
                           (env1.FStarC_TypeChecker_Env.gamma_sig);
                         FStarC_TypeChecker_Env.gamma_cache =
                           (env1.FStarC_TypeChecker_Env.gamma_cache);
                         FStarC_TypeChecker_Env.modules =
                           (env1.FStarC_TypeChecker_Env.modules);
                         FStarC_TypeChecker_Env.expected_typ =
                           (env1.FStarC_TypeChecker_Env.expected_typ);
                         FStarC_TypeChecker_Env.sigtab =
                           (env1.FStarC_TypeChecker_Env.sigtab);
                         FStarC_TypeChecker_Env.attrtab =
                           (env1.FStarC_TypeChecker_Env.attrtab);
                         FStarC_TypeChecker_Env.instantiate_imp =
                           (env1.FStarC_TypeChecker_Env.instantiate_imp);
                         FStarC_TypeChecker_Env.effects =
                           (env1.FStarC_TypeChecker_Env.effects);
                         FStarC_TypeChecker_Env.generalize =
                           (env1.FStarC_TypeChecker_Env.generalize);
                         FStarC_TypeChecker_Env.letrecs =
                           (env1.FStarC_TypeChecker_Env.letrecs);
                         FStarC_TypeChecker_Env.top_level =
                           (env1.FStarC_TypeChecker_Env.top_level);
                         FStarC_TypeChecker_Env.check_uvars =
                           (env1.FStarC_TypeChecker_Env.check_uvars);
                         FStarC_TypeChecker_Env.use_eq_strict =
                           (env1.FStarC_TypeChecker_Env.use_eq_strict);
                         FStarC_TypeChecker_Env.is_iface =
                           (env1.FStarC_TypeChecker_Env.is_iface);
                         FStarC_TypeChecker_Env.admit =
                           (env1.FStarC_TypeChecker_Env.admit);
                         FStarC_TypeChecker_Env.lax_universes =
                           (env1.FStarC_TypeChecker_Env.lax_universes);
                         FStarC_TypeChecker_Env.phase1 =
                           (env1.FStarC_TypeChecker_Env.phase1);
                         FStarC_TypeChecker_Env.failhard =
                           (env1.FStarC_TypeChecker_Env.failhard);
                         FStarC_TypeChecker_Env.flychecking =
                           (env1.FStarC_TypeChecker_Env.flychecking);
                         FStarC_TypeChecker_Env.uvar_subtyping =
                           (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                         FStarC_TypeChecker_Env.intactics =
                           (env1.FStarC_TypeChecker_Env.intactics);
                         FStarC_TypeChecker_Env.nocoerce =
                           (env1.FStarC_TypeChecker_Env.nocoerce);
                         FStarC_TypeChecker_Env.tc_term =
                           (env1.FStarC_TypeChecker_Env.tc_term);
                         FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                           (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                         FStarC_TypeChecker_Env.universe_of =
                           (env1.FStarC_TypeChecker_Env.universe_of);
                         FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                           =
                           (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                         FStarC_TypeChecker_Env.teq_nosmt_force =
                           (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                         FStarC_TypeChecker_Env.subtype_nosmt_force =
                           (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                         FStarC_TypeChecker_Env.qtbl_name_and_index =
                           (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                         FStarC_TypeChecker_Env.normalized_eff_names =
                           (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                         FStarC_TypeChecker_Env.fv_delta_depths =
                           (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                         FStarC_TypeChecker_Env.proof_ns =
                           (env1.FStarC_TypeChecker_Env.proof_ns);
                         FStarC_TypeChecker_Env.synth_hook =
                           (env1.FStarC_TypeChecker_Env.synth_hook);
                         FStarC_TypeChecker_Env.try_solve_implicits_hook =
                           (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                         FStarC_TypeChecker_Env.splice =
                           (env1.FStarC_TypeChecker_Env.splice);
                         FStarC_TypeChecker_Env.mpreprocess =
                           (env1.FStarC_TypeChecker_Env.mpreprocess);
                         FStarC_TypeChecker_Env.postprocess =
                           (env1.FStarC_TypeChecker_Env.postprocess);
                         FStarC_TypeChecker_Env.identifier_info =
                           (env1.FStarC_TypeChecker_Env.identifier_info);
                         FStarC_TypeChecker_Env.tc_hooks =
                           (env1.FStarC_TypeChecker_Env.tc_hooks);
                         FStarC_TypeChecker_Env.dsenv =
                           (env1.FStarC_TypeChecker_Env.dsenv);
                         FStarC_TypeChecker_Env.nbe =
                           (env1.FStarC_TypeChecker_Env.nbe);
                         FStarC_TypeChecker_Env.strict_args_tab =
                           (env1.FStarC_TypeChecker_Env.strict_args_tab);
                         FStarC_TypeChecker_Env.erasable_types_tab =
                           (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                         FStarC_TypeChecker_Env.enable_defer_to_tac =
                           (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                         FStarC_TypeChecker_Env.unif_allow_ref_guards =
                           (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                         FStarC_TypeChecker_Env.erase_erasable_args =
                           (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                         FStarC_TypeChecker_Env.core_check =
                           (env1.FStarC_TypeChecker_Env.core_check);
                         FStarC_TypeChecker_Env.missing_decl =
                           (env1.FStarC_TypeChecker_Env.missing_decl)
                       } in
                     let must_tot1 =
                       must_tot &&
                         (Prims.op_Negation
                            (FStarC_Syntax_Syntax.uu___is_Allow_ghost
                               dec.FStarC_Syntax_Syntax.uvar_decoration_should_check)) in
                     let uu___2 =
                       let uu___3 = FStarC_Syntax_Util.ctx_uvar_typ u in
                       core_check env2 sol uu___3 must_tot1 in
                     (match uu___2 with
                      | FStar_Pervasives.Inl (FStar_Pervasives_Native.None)
                          -> (mark_uvar_as_already_checked u; ret ())
                      | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g)
                          ->
                          let guard =
                            {
                              FStarC_TypeChecker_Common.guard_f =
                                (FStarC_TypeChecker_Common.NonTrivial g);
                              FStarC_TypeChecker_Common.deferred_to_tac =
                                (FStarC_TypeChecker_Env.trivial_guard.FStarC_TypeChecker_Common.deferred_to_tac);
                              FStarC_TypeChecker_Common.deferred =
                                (FStarC_TypeChecker_Env.trivial_guard.FStarC_TypeChecker_Common.deferred);
                              FStarC_TypeChecker_Common.univ_ineqs =
                                (FStarC_TypeChecker_Env.trivial_guard.FStarC_TypeChecker_Common.univ_ineqs);
                              FStarC_TypeChecker_Common.implicits =
                                (FStarC_TypeChecker_Env.trivial_guard.FStarC_TypeChecker_Common.implicits)
                            } in
                          let guard1 =
                            FStarC_TypeChecker_Rel.simplify_guard env2 guard in
                          let uu___3 =
                            ((FStarC_Options.disallow_unification_guards ())
                               && (Prims.op_Negation allow_guards))
                              &&
                              (FStarC_TypeChecker_Common.uu___is_NonTrivial
                                 guard1.FStarC_TypeChecker_Common.guard_f) in
                          if uu___3
                          then
                            let uu___4 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_uvar
                                u.FStarC_Syntax_Syntax.ctx_uvar_head in
                            let uu___5 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_term sol in
                            let uu___6 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_term g in
                            fail3
                              "Could not typecheck unifier solved implicit %s to %s since it produced a guard and guards were not allowed;guard is\n%s"
                              uu___4 uu___5 uu___6
                          else
                            (let uu___5 =
                               proc_guard' false "guard for implicit" env2
                                 guard1 (FStar_Pervasives_Native.Some sc)
                                 u.FStarC_Syntax_Syntax.ctx_uvar_range in
                             FStarC_Class_Monad.op_let_Bang
                               FStarC_Tactics_Monad.monad_tac () () uu___5
                               (fun uu___6 ->
                                  (fun uu___6 ->
                                     let uu___6 = Obj.magic uu___6 in
                                     mark_uvar_as_already_checked u;
                                     Obj.magic (ret ())) uu___6))
                      | FStar_Pervasives.Inr failed ->
                          let uu___3 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_uvar
                              u.FStarC_Syntax_Syntax.ctx_uvar_head in
                          let uu___4 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term sol in
                          let uu___5 =
                            FStarC_TypeChecker_Core.print_error failed in
                          fail3
                            "Could not typecheck unifier solved implicit %s to %s because %s"
                            uu___3 uu___4 uu___5)) in
          if env1.FStarC_TypeChecker_Env.phase1
          then ret ()
          else FStarC_Tactics_Monad.iter_tac aux uvs
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
            FStarC_Syntax_Syntax.term ->
              FStarC_Syntax_Syntax.term ->
                FStarC_TypeChecker_Common.guard_t
                  FStar_Pervasives_Native.option FStarC_Tactics_Monad.tac)
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
                                    FStarC_Class_Show.show
                                      FStarC_Syntax_Print.showable_term t1 in
                                  let uu___2 =
                                    FStarC_Class_Show.show
                                      FStarC_Syntax_Print.showable_term t2 in
                                  FStarC_Compiler_Util.print2
                                    "%%%%%%%%do_unify %s =? %s\n" uu___1
                                    uu___2)
                               else ();
                               (let all_uvars =
                                  let uu___1 =
                                    match check_side with
                                    | Check_none ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStarC_Class_Setlike.empty ()
                                                (Obj.magic
                                                   (FStarC_Compiler_FlatSet.setlike_flat_set
                                                      FStarC_Syntax_Free.ord_ctx_uvar))
                                                ()))
                                    | Check_left_only ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStarC_Syntax_Free.uvars t1))
                                    | Check_right_only ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStarC_Syntax_Free.uvars t2))
                                    | Check_both ->
                                        Obj.magic
                                          (Obj.repr
                                             (let uu___2 =
                                                FStarC_Syntax_Free.uvars t1 in
                                              let uu___3 =
                                                FStarC_Syntax_Free.uvars t2 in
                                              FStarC_Class_Setlike.union ()
                                                (Obj.magic
                                                   (FStarC_Compiler_FlatSet.setlike_flat_set
                                                      FStarC_Syntax_Free.ord_ctx_uvar))
                                                (Obj.magic uu___2)
                                                (Obj.magic uu___3))) in
                                  FStarC_Class_Setlike.elems ()
                                    (Obj.magic
                                       (FStarC_Compiler_FlatSet.setlike_flat_set
                                          FStarC_Syntax_Free.ord_ctx_uvar))
                                    (Obj.magic uu___1) in
                                let uu___1 =
                                  let uu___2 =
                                    let uu___3 =
                                      FStarC_Tactics_Monad.trytac
                                        FStarC_Tactics_Monad.cur_goal in
                                    let uu___4 = bind () in
                                    uu___4 uu___3
                                      (fun gopt ->
                                         try
                                           (fun uu___5 ->
                                              (fun uu___5 ->
                                                 match () with
                                                 | () ->
                                                     let res =
                                                       if allow_guards
                                                       then
                                                         FStarC_TypeChecker_Rel.try_teq
                                                           true env1 t1 t2
                                                       else
                                                         FStarC_TypeChecker_Rel.teq_nosmt
                                                           env1 t1 t2 in
                                                     (if dbg
                                                      then
                                                        (let uu___7 =
                                                           FStarC_Common.string_of_option
                                                             (FStarC_TypeChecker_Rel.guard_to_string
                                                                env1) res in
                                                         let uu___8 =
                                                           FStarC_Class_Show.show
                                                             FStarC_Syntax_Print.showable_term
                                                             t1 in
                                                         let uu___9 =
                                                           FStarC_Class_Show.show
                                                             FStarC_Syntax_Print.showable_term
                                                             t2 in
                                                         FStarC_Compiler_Util.print3
                                                           "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                                                           uu___7 uu___8
                                                           uu___9)
                                                      else ();
                                                      (match res with
                                                       | FStar_Pervasives_Native.None
                                                           ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (ret
                                                                   FStar_Pervasives_Native.None))
                                                       | FStar_Pervasives_Native.Some
                                                           g ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (let uu___7 =
                                                                   tc_unifier_solved_implicits
                                                                    env1
                                                                    must_tot
                                                                    allow_guards
                                                                    all_uvars in
                                                                 FStarC_Class_Monad.op_let_Bang
                                                                   FStarC_Tactics_Monad.monad_tac
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
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    FStarC_Class_Listlike.to_list
                                                                    (FStarC_Compiler_CList.listlike_clist
                                                                    ())
                                                                    g.FStarC_TypeChecker_Common.implicits in
                                                                    FStarC_Tactics_Monad.add_implicits
                                                                    uu___10 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    (ret
                                                                    (FStar_Pervasives_Native.Some
                                                                    g)))
                                                                    uu___10)))
                                                                    uu___8))))))
                                                uu___5) ()
                                         with
                                         | FStarC_Errors.Error
                                             (uu___6, msg, r, uu___7) ->
                                             FStarC_Tactics_Monad.mlog
                                               (fun uu___8 ->
                                                  let uu___9 =
                                                    FStarC_Errors_Msg.rendermsg
                                                      msg in
                                                  let uu___10 =
                                                    FStarC_Class_Show.show
                                                      FStarC_Compiler_Range_Ops.showable_range
                                                      r in
                                                  FStarC_Compiler_Util.print2
                                                    ">> do_unify error, (%s) at (%s)\n"
                                                    uu___9 uu___10)
                                               (fun uu___8 ->
                                                  ret
                                                    FStar_Pervasives_Native.None)) in
                                  FStarC_Tactics_Monad.catch uu___2 in
                                Obj.magic
                                  (FStarC_Class_Monad.op_let_Bang
                                     FStarC_Tactics_Monad.monad_tac () ()
                                     (Obj.magic uu___1)
                                     (fun uu___2 ->
                                        (fun uu___2 ->
                                           let uu___2 = Obj.magic uu___2 in
                                           match uu___2 with
                                           | FStar_Pervasives.Inl exn ->
                                               Obj.magic
                                                 (FStarC_Tactics_Monad.traise
                                                    exn)
                                           | FStar_Pervasives.Inr v ->
                                               Obj.magic (ret v)) uu___2))))
                  uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (__do_unify :
  Prims.bool ->
    Prims.bool ->
      check_unifier_solved_implicits_side ->
        env ->
          FStarC_Syntax_Syntax.term ->
            FStarC_Syntax_Syntax.term ->
              FStarC_TypeChecker_Common.guard_t
                FStar_Pervasives_Native.option FStarC_Tactics_Monad.tac)
  =
  fun allow_guards ->
    fun must_tot ->
      fun check_side ->
        fun env1 ->
          fun t1 ->
            fun t2 ->
              let uu___ = bind () in
              uu___ idtac
                (fun uu___1 ->
                   (let uu___3 = FStarC_Compiler_Effect.op_Bang dbg_TacUnify in
                    if uu___3
                    then
                      (FStarC_Options.push ();
                       (let uu___5 =
                          FStarC_Options.set_options "--debug Rel,RelCheck" in
                        ()))
                    else ());
                   (let uu___3 =
                      let uu___4 =
                        FStarC_Compiler_Effect.op_Bang dbg_TacUnify in
                      __do_unify_wflags uu___4 allow_guards must_tot
                        check_side env1 t1 t2 in
                    let uu___4 = bind () in
                    uu___4 uu___3
                      (fun r ->
                         (let uu___6 =
                            FStarC_Compiler_Effect.op_Bang dbg_TacUnify in
                          if uu___6 then FStarC_Options.pop () else ());
                         ret r)))
let (do_unify_aux :
  Prims.bool ->
    check_unifier_solved_implicits_side ->
      env ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Syntax_Syntax.term -> Prims.bool FStarC_Tactics_Monad.tac)
  =
  fun must_tot ->
    fun check_side ->
      fun env1 ->
        fun t1 ->
          fun t2 ->
            let uu___ = __do_unify false must_tot check_side env1 t1 t2 in
            let uu___1 = bind () in
            uu___1 uu___
              (fun uu___2 ->
                 match uu___2 with
                 | FStar_Pervasives_Native.None -> ret false
                 | FStar_Pervasives_Native.Some g ->
                     ((let uu___4 =
                         let uu___5 =
                           FStarC_TypeChecker_Env.is_trivial_guard_formula g in
                         Prims.op_Negation uu___5 in
                       if uu___4
                       then
                         failwith
                           "internal error: do_unify: guard is not trivial"
                       else ());
                      ret true))
let (do_unify :
  Prims.bool ->
    env ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.term -> Prims.bool FStarC_Tactics_Monad.tac)
  =
  fun must_tot ->
    fun env1 ->
      fun t1 -> fun t2 -> do_unify_aux must_tot Check_both env1 t1 t2
let (do_unify_maybe_guards :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Syntax_Syntax.term ->
            FStarC_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
              FStarC_Tactics_Monad.tac)
  =
  fun allow_guards ->
    fun must_tot ->
      fun env1 ->
        fun t1 ->
          fun t2 -> __do_unify allow_guards must_tot Check_both env1 t1 t2
let (do_match :
  Prims.bool ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.term -> Prims.bool FStarC_Tactics_Monad.tac)
  =
  fun must_tot ->
    fun env1 ->
      fun t1 ->
        fun t2 ->
          let uu___ =
            FStarC_Tactics_Monad.mk_tac
              (fun ps ->
                 let tx = FStarC_Syntax_Unionfind.new_transaction () in
                 FStarC_Tactics_Result.Success (tx, ps)) in
          let uu___1 = bind () in
          uu___1 uu___
            (fun tx ->
               let uvs1 = FStarC_Syntax_Free.uvars_uncached t1 in
               let uu___2 = do_unify_aux must_tot Check_right_only env1 t1 t2 in
               let uu___3 = bind () in
               uu___3 uu___2
                 (fun r ->
                    if r
                    then
                      let uvs2 = FStarC_Syntax_Free.uvars_uncached t1 in
                      let uu___4 =
                        let uu___5 =
                          FStarC_Class_Setlike.equal ()
                            (Obj.magic
                               (FStarC_Compiler_FlatSet.setlike_flat_set
                                  FStarC_Syntax_Free.ord_ctx_uvar))
                            (Obj.magic uvs1) (Obj.magic uvs2) in
                        Prims.op_Negation uu___5 in
                      (if uu___4
                       then (FStarC_Syntax_Unionfind.rollback tx; ret false)
                       else ret true)
                    else ret false))
let (do_match_on_lhs :
  Prims.bool ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.term -> Prims.bool FStarC_Tactics_Monad.tac)
  =
  fun must_tot ->
    fun env1 ->
      fun t1 ->
        fun t2 ->
          let uu___ =
            FStarC_Tactics_Monad.mk_tac
              (fun ps ->
                 let tx = FStarC_Syntax_Unionfind.new_transaction () in
                 FStarC_Tactics_Result.Success (tx, ps)) in
          let uu___1 = bind () in
          uu___1 uu___
            (fun tx ->
               let uu___2 = destruct_eq env1 t1 in
               match uu___2 with
               | FStar_Pervasives_Native.None ->
                   FStarC_Tactics_Monad.fail "do_match_on_lhs: not an eq"
               | FStar_Pervasives_Native.Some (lhs, uu___3) ->
                   let uvs1 = FStarC_Syntax_Free.uvars_uncached lhs in
                   let uu___4 =
                     do_unify_aux must_tot Check_right_only env1 t1 t2 in
                   let uu___5 = bind () in
                   uu___5 uu___4
                     (fun r ->
                        if r
                        then
                          let uvs2 = FStarC_Syntax_Free.uvars_uncached lhs in
                          let uu___6 =
                            let uu___7 =
                              FStarC_Class_Setlike.equal ()
                                (Obj.magic
                                   (FStarC_Compiler_FlatSet.setlike_flat_set
                                      FStarC_Syntax_Free.ord_ctx_uvar))
                                (Obj.magic uvs1) (Obj.magic uvs2) in
                            Prims.op_Negation uu___7 in
                          (if uu___6
                           then
                             (FStarC_Syntax_Unionfind.rollback tx; ret false)
                           else ret true)
                        else ret false))
let (set_solution :
  FStarC_Tactics_Types.goal ->
    FStarC_Syntax_Syntax.term -> unit FStarC_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu___ =
        FStarC_Syntax_Unionfind.find
          (goal.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_head in
      match uu___ with
      | FStar_Pervasives_Native.Some uu___1 ->
          let uu___2 =
            let uu___3 = FStarC_Tactics_Printing.goal_to_string_verbose goal in
            FStarC_Compiler_Util.format1 "Goal %s is already solved" uu___3 in
          FStarC_Tactics_Monad.fail uu___2
      | FStar_Pervasives_Native.None ->
          (FStarC_Syntax_Unionfind.change
             (goal.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_head
             solution;
           mark_goal_implicit_already_checked goal;
           ret ())
let (trysolve :
  FStarC_Tactics_Types.goal ->
    FStarC_Syntax_Syntax.term -> Prims.bool FStarC_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let must_tot = true in
      let uu___ = FStarC_Tactics_Types.goal_env goal in
      let uu___1 = FStarC_Tactics_Types.goal_witness goal in
      do_unify must_tot uu___ solution uu___1
let (solve :
  FStarC_Tactics_Types.goal ->
    FStarC_Syntax_Syntax.term -> unit FStarC_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let e = FStarC_Tactics_Types.goal_env goal in
      FStarC_Tactics_Monad.mlog
        (fun uu___ ->
           let uu___1 =
             let uu___2 = FStarC_Tactics_Types.goal_witness goal in
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term uu___2 in
           let uu___2 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
               solution in
           FStarC_Compiler_Util.print2 "solve %s := %s\n" uu___1 uu___2)
        (fun uu___ ->
           let uu___1 = trysolve goal solution in
           let uu___2 = bind () in
           uu___2 uu___1
             (fun b ->
                if b
                then
                  let uu___3 = bind () in
                  uu___3 FStarC_Tactics_Monad.dismiss
                    (fun uu___4 -> FStarC_Tactics_Monad.remove_solved_goals)
                else
                  (let uu___4 =
                     let uu___5 =
                       let uu___6 = FStarC_Tactics_Types.goal_env goal in
                       tts uu___6 solution in
                     let uu___6 =
                       let uu___7 = FStarC_Tactics_Types.goal_env goal in
                       let uu___8 = FStarC_Tactics_Types.goal_witness goal in
                       tts uu___7 uu___8 in
                     let uu___7 =
                       let uu___8 = FStarC_Tactics_Types.goal_env goal in
                       let uu___9 = FStarC_Tactics_Types.goal_type goal in
                       tts uu___8 uu___9 in
                     FStarC_Compiler_Util.format3 "%s does not solve %s : %s"
                       uu___5 uu___6 uu___7 in
                   FStarC_Tactics_Monad.fail uu___4)))
let (solve' :
  FStarC_Tactics_Types.goal ->
    FStarC_Syntax_Syntax.term -> unit FStarC_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu___ = set_solution goal solution in
      let uu___1 = bind () in
      uu___1 uu___
        (fun uu___2 ->
           let uu___3 = bind () in
           uu___3 FStarC_Tactics_Monad.dismiss
             (fun uu___4 -> FStarC_Tactics_Monad.remove_solved_goals))
let (is_true : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let t1 = FStarC_Syntax_Util.unascribe t in
    let uu___ = FStarC_Syntax_Util.un_squash t1 in
    match uu___ with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStarC_Syntax_Util.unascribe t' in
        let uu___1 =
          let uu___2 = FStarC_Syntax_Subst.compress t'1 in
          uu___2.FStarC_Syntax_Syntax.n in
        (match uu___1 with
         | FStarC_Syntax_Syntax.Tm_fvar fv ->
             FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.true_lid
         | uu___2 -> false)
    | uu___1 -> false
let (is_false : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = FStarC_Syntax_Util.un_squash t in
    match uu___ with
    | FStar_Pervasives_Native.Some t' ->
        let uu___1 =
          let uu___2 = FStarC_Syntax_Subst.compress t' in
          uu___2.FStarC_Syntax_Syntax.n in
        (match uu___1 with
         | FStarC_Syntax_Syntax.Tm_fvar fv ->
             FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.false_lid
         | uu___2 -> false)
    | uu___1 -> false
let (tadmit_t : FStarC_Syntax_Syntax.term -> unit FStarC_Tactics_Monad.tac) =
  fun t ->
    let uu___ =
      let uu___1 = bind () in
      uu___1 FStarC_Tactics_Monad.get
        (fun ps ->
           let uu___2 = bind () in
           uu___2 FStarC_Tactics_Monad.cur_goal
             (fun g ->
                (let uu___4 = FStarC_Tactics_Types.goal_type g in
                 let uu___5 =
                   let uu___6 =
                     FStarC_Tactics_Printing.goal_to_string ""
                       FStar_Pervasives_Native.None ps g in
                   FStarC_Compiler_Util.format1
                     "Tactics admitted goal <%s>\n\n" uu___6 in
                 FStarC_Errors.log_issue
                   (FStarC_Syntax_Syntax.has_range_syntax ()) uu___4
                   FStarC_Errors_Codes.Warning_TacAdmit ()
                   (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                   (Obj.magic uu___5));
                solve' g t)) in
    FStarC_Tactics_Monad.wrap_err "tadmit_t" uu___
let (fresh : unit -> FStarC_BigInt.t FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 = bind () in
    uu___1 FStarC_Tactics_Monad.get
      (fun ps ->
         let n = ps.FStarC_Tactics_Types.freshness in
         let ps1 =
           {
             FStarC_Tactics_Types.main_context =
               (ps.FStarC_Tactics_Types.main_context);
             FStarC_Tactics_Types.all_implicits =
               (ps.FStarC_Tactics_Types.all_implicits);
             FStarC_Tactics_Types.goals = (ps.FStarC_Tactics_Types.goals);
             FStarC_Tactics_Types.smt_goals =
               (ps.FStarC_Tactics_Types.smt_goals);
             FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
             FStarC_Tactics_Types.__dump = (ps.FStarC_Tactics_Types.__dump);
             FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
             FStarC_Tactics_Types.entry_range =
               (ps.FStarC_Tactics_Types.entry_range);
             FStarC_Tactics_Types.guard_policy =
               (ps.FStarC_Tactics_Types.guard_policy);
             FStarC_Tactics_Types.freshness = (n + Prims.int_one);
             FStarC_Tactics_Types.tac_verb_dbg =
               (ps.FStarC_Tactics_Types.tac_verb_dbg);
             FStarC_Tactics_Types.local_state =
               (ps.FStarC_Tactics_Types.local_state);
             FStarC_Tactics_Types.urgency = (ps.FStarC_Tactics_Types.urgency);
             FStarC_Tactics_Types.dump_on_failure =
               (ps.FStarC_Tactics_Types.dump_on_failure)
           } in
         let uu___2 = FStarC_Tactics_Monad.set ps1 in
         let uu___3 = bind () in
         uu___3 uu___2
           (fun uu___4 ->
              let uu___5 = FStarC_BigInt.of_int_fs n in ret uu___5))
let (curms : unit -> FStarC_BigInt.t FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStarC_Compiler_Util.now_ms () in
      FStarC_BigInt.of_int_fs uu___2 in
    ret uu___1
let (__tc :
  env ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.typ *
        FStarC_TypeChecker_Common.guard_t) FStarC_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu___ = bind () in
      uu___ FStarC_Tactics_Monad.get
        (fun ps ->
           FStarC_Tactics_Monad.mlog
             (fun uu___1 ->
                let uu___2 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
                FStarC_Compiler_Util.print1 "Tac> __tc(%s)\n" uu___2)
             (fun uu___1 ->
                let e1 =
                  {
                    FStarC_TypeChecker_Env.solver =
                      (e.FStarC_TypeChecker_Env.solver);
                    FStarC_TypeChecker_Env.range =
                      (e.FStarC_TypeChecker_Env.range);
                    FStarC_TypeChecker_Env.curmodule =
                      (e.FStarC_TypeChecker_Env.curmodule);
                    FStarC_TypeChecker_Env.gamma =
                      (e.FStarC_TypeChecker_Env.gamma);
                    FStarC_TypeChecker_Env.gamma_sig =
                      (e.FStarC_TypeChecker_Env.gamma_sig);
                    FStarC_TypeChecker_Env.gamma_cache =
                      (e.FStarC_TypeChecker_Env.gamma_cache);
                    FStarC_TypeChecker_Env.modules =
                      (e.FStarC_TypeChecker_Env.modules);
                    FStarC_TypeChecker_Env.expected_typ =
                      (e.FStarC_TypeChecker_Env.expected_typ);
                    FStarC_TypeChecker_Env.sigtab =
                      (e.FStarC_TypeChecker_Env.sigtab);
                    FStarC_TypeChecker_Env.attrtab =
                      (e.FStarC_TypeChecker_Env.attrtab);
                    FStarC_TypeChecker_Env.instantiate_imp =
                      (e.FStarC_TypeChecker_Env.instantiate_imp);
                    FStarC_TypeChecker_Env.effects =
                      (e.FStarC_TypeChecker_Env.effects);
                    FStarC_TypeChecker_Env.generalize =
                      (e.FStarC_TypeChecker_Env.generalize);
                    FStarC_TypeChecker_Env.letrecs =
                      (e.FStarC_TypeChecker_Env.letrecs);
                    FStarC_TypeChecker_Env.top_level =
                      (e.FStarC_TypeChecker_Env.top_level);
                    FStarC_TypeChecker_Env.check_uvars =
                      (e.FStarC_TypeChecker_Env.check_uvars);
                    FStarC_TypeChecker_Env.use_eq_strict =
                      (e.FStarC_TypeChecker_Env.use_eq_strict);
                    FStarC_TypeChecker_Env.is_iface =
                      (e.FStarC_TypeChecker_Env.is_iface);
                    FStarC_TypeChecker_Env.admit =
                      (e.FStarC_TypeChecker_Env.admit);
                    FStarC_TypeChecker_Env.lax_universes =
                      (e.FStarC_TypeChecker_Env.lax_universes);
                    FStarC_TypeChecker_Env.phase1 =
                      (e.FStarC_TypeChecker_Env.phase1);
                    FStarC_TypeChecker_Env.failhard =
                      (e.FStarC_TypeChecker_Env.failhard);
                    FStarC_TypeChecker_Env.flychecking =
                      (e.FStarC_TypeChecker_Env.flychecking);
                    FStarC_TypeChecker_Env.uvar_subtyping = false;
                    FStarC_TypeChecker_Env.intactics =
                      (e.FStarC_TypeChecker_Env.intactics);
                    FStarC_TypeChecker_Env.nocoerce =
                      (e.FStarC_TypeChecker_Env.nocoerce);
                    FStarC_TypeChecker_Env.tc_term =
                      (e.FStarC_TypeChecker_Env.tc_term);
                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                      (e.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                    FStarC_TypeChecker_Env.universe_of =
                      (e.FStarC_TypeChecker_Env.universe_of);
                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                      =
                      (e.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                    FStarC_TypeChecker_Env.teq_nosmt_force =
                      (e.FStarC_TypeChecker_Env.teq_nosmt_force);
                    FStarC_TypeChecker_Env.subtype_nosmt_force =
                      (e.FStarC_TypeChecker_Env.subtype_nosmt_force);
                    FStarC_TypeChecker_Env.qtbl_name_and_index =
                      (e.FStarC_TypeChecker_Env.qtbl_name_and_index);
                    FStarC_TypeChecker_Env.normalized_eff_names =
                      (e.FStarC_TypeChecker_Env.normalized_eff_names);
                    FStarC_TypeChecker_Env.fv_delta_depths =
                      (e.FStarC_TypeChecker_Env.fv_delta_depths);
                    FStarC_TypeChecker_Env.proof_ns =
                      (e.FStarC_TypeChecker_Env.proof_ns);
                    FStarC_TypeChecker_Env.synth_hook =
                      (e.FStarC_TypeChecker_Env.synth_hook);
                    FStarC_TypeChecker_Env.try_solve_implicits_hook =
                      (e.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                    FStarC_TypeChecker_Env.splice =
                      (e.FStarC_TypeChecker_Env.splice);
                    FStarC_TypeChecker_Env.mpreprocess =
                      (e.FStarC_TypeChecker_Env.mpreprocess);
                    FStarC_TypeChecker_Env.postprocess =
                      (e.FStarC_TypeChecker_Env.postprocess);
                    FStarC_TypeChecker_Env.identifier_info =
                      (e.FStarC_TypeChecker_Env.identifier_info);
                    FStarC_TypeChecker_Env.tc_hooks =
                      (e.FStarC_TypeChecker_Env.tc_hooks);
                    FStarC_TypeChecker_Env.dsenv =
                      (e.FStarC_TypeChecker_Env.dsenv);
                    FStarC_TypeChecker_Env.nbe =
                      (e.FStarC_TypeChecker_Env.nbe);
                    FStarC_TypeChecker_Env.strict_args_tab =
                      (e.FStarC_TypeChecker_Env.strict_args_tab);
                    FStarC_TypeChecker_Env.erasable_types_tab =
                      (e.FStarC_TypeChecker_Env.erasable_types_tab);
                    FStarC_TypeChecker_Env.enable_defer_to_tac =
                      (e.FStarC_TypeChecker_Env.enable_defer_to_tac);
                    FStarC_TypeChecker_Env.unif_allow_ref_guards =
                      (e.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                    FStarC_TypeChecker_Env.erase_erasable_args =
                      (e.FStarC_TypeChecker_Env.erase_erasable_args);
                    FStarC_TypeChecker_Env.core_check =
                      (e.FStarC_TypeChecker_Env.core_check);
                    FStarC_TypeChecker_Env.missing_decl =
                      (e.FStarC_TypeChecker_Env.missing_decl)
                  } in
                try
                  (fun uu___2 ->
                     match () with
                     | () ->
                         let uu___3 =
                           FStarC_TypeChecker_TcTerm.typeof_tot_or_gtot_term
                             e1 t true in
                         ret uu___3) ()
                with
                | FStarC_Errors.Error (uu___3, msg, uu___4, uu___5) ->
                    let uu___6 = tts e1 t in
                    let uu___7 =
                      let uu___8 = FStarC_TypeChecker_Env.all_binders e1 in
                      FStarC_Class_Show.show
                        (FStarC_Class_Show.show_list
                           FStarC_Syntax_Print.showable_binder) uu___8 in
                    let uu___8 = FStarC_Errors_Msg.rendermsg msg in
                    fail3 "Cannot type (1) %s in context (%s). Error = (%s)"
                      uu___6 uu___7 uu___8))
let (__tc_ghost :
  env ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.typ *
        FStarC_TypeChecker_Common.guard_t) FStarC_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu___ = bind () in
      uu___ FStarC_Tactics_Monad.get
        (fun ps ->
           FStarC_Tactics_Monad.mlog
             (fun uu___1 ->
                let uu___2 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
                FStarC_Compiler_Util.print1 "Tac> __tc_ghost(%s)\n" uu___2)
             (fun uu___1 ->
                let e1 =
                  {
                    FStarC_TypeChecker_Env.solver =
                      (e.FStarC_TypeChecker_Env.solver);
                    FStarC_TypeChecker_Env.range =
                      (e.FStarC_TypeChecker_Env.range);
                    FStarC_TypeChecker_Env.curmodule =
                      (e.FStarC_TypeChecker_Env.curmodule);
                    FStarC_TypeChecker_Env.gamma =
                      (e.FStarC_TypeChecker_Env.gamma);
                    FStarC_TypeChecker_Env.gamma_sig =
                      (e.FStarC_TypeChecker_Env.gamma_sig);
                    FStarC_TypeChecker_Env.gamma_cache =
                      (e.FStarC_TypeChecker_Env.gamma_cache);
                    FStarC_TypeChecker_Env.modules =
                      (e.FStarC_TypeChecker_Env.modules);
                    FStarC_TypeChecker_Env.expected_typ =
                      (e.FStarC_TypeChecker_Env.expected_typ);
                    FStarC_TypeChecker_Env.sigtab =
                      (e.FStarC_TypeChecker_Env.sigtab);
                    FStarC_TypeChecker_Env.attrtab =
                      (e.FStarC_TypeChecker_Env.attrtab);
                    FStarC_TypeChecker_Env.instantiate_imp =
                      (e.FStarC_TypeChecker_Env.instantiate_imp);
                    FStarC_TypeChecker_Env.effects =
                      (e.FStarC_TypeChecker_Env.effects);
                    FStarC_TypeChecker_Env.generalize =
                      (e.FStarC_TypeChecker_Env.generalize);
                    FStarC_TypeChecker_Env.letrecs =
                      (e.FStarC_TypeChecker_Env.letrecs);
                    FStarC_TypeChecker_Env.top_level =
                      (e.FStarC_TypeChecker_Env.top_level);
                    FStarC_TypeChecker_Env.check_uvars =
                      (e.FStarC_TypeChecker_Env.check_uvars);
                    FStarC_TypeChecker_Env.use_eq_strict =
                      (e.FStarC_TypeChecker_Env.use_eq_strict);
                    FStarC_TypeChecker_Env.is_iface =
                      (e.FStarC_TypeChecker_Env.is_iface);
                    FStarC_TypeChecker_Env.admit =
                      (e.FStarC_TypeChecker_Env.admit);
                    FStarC_TypeChecker_Env.lax_universes =
                      (e.FStarC_TypeChecker_Env.lax_universes);
                    FStarC_TypeChecker_Env.phase1 =
                      (e.FStarC_TypeChecker_Env.phase1);
                    FStarC_TypeChecker_Env.failhard =
                      (e.FStarC_TypeChecker_Env.failhard);
                    FStarC_TypeChecker_Env.flychecking =
                      (e.FStarC_TypeChecker_Env.flychecking);
                    FStarC_TypeChecker_Env.uvar_subtyping = false;
                    FStarC_TypeChecker_Env.intactics =
                      (e.FStarC_TypeChecker_Env.intactics);
                    FStarC_TypeChecker_Env.nocoerce =
                      (e.FStarC_TypeChecker_Env.nocoerce);
                    FStarC_TypeChecker_Env.tc_term =
                      (e.FStarC_TypeChecker_Env.tc_term);
                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                      (e.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                    FStarC_TypeChecker_Env.universe_of =
                      (e.FStarC_TypeChecker_Env.universe_of);
                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                      =
                      (e.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                    FStarC_TypeChecker_Env.teq_nosmt_force =
                      (e.FStarC_TypeChecker_Env.teq_nosmt_force);
                    FStarC_TypeChecker_Env.subtype_nosmt_force =
                      (e.FStarC_TypeChecker_Env.subtype_nosmt_force);
                    FStarC_TypeChecker_Env.qtbl_name_and_index =
                      (e.FStarC_TypeChecker_Env.qtbl_name_and_index);
                    FStarC_TypeChecker_Env.normalized_eff_names =
                      (e.FStarC_TypeChecker_Env.normalized_eff_names);
                    FStarC_TypeChecker_Env.fv_delta_depths =
                      (e.FStarC_TypeChecker_Env.fv_delta_depths);
                    FStarC_TypeChecker_Env.proof_ns =
                      (e.FStarC_TypeChecker_Env.proof_ns);
                    FStarC_TypeChecker_Env.synth_hook =
                      (e.FStarC_TypeChecker_Env.synth_hook);
                    FStarC_TypeChecker_Env.try_solve_implicits_hook =
                      (e.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                    FStarC_TypeChecker_Env.splice =
                      (e.FStarC_TypeChecker_Env.splice);
                    FStarC_TypeChecker_Env.mpreprocess =
                      (e.FStarC_TypeChecker_Env.mpreprocess);
                    FStarC_TypeChecker_Env.postprocess =
                      (e.FStarC_TypeChecker_Env.postprocess);
                    FStarC_TypeChecker_Env.identifier_info =
                      (e.FStarC_TypeChecker_Env.identifier_info);
                    FStarC_TypeChecker_Env.tc_hooks =
                      (e.FStarC_TypeChecker_Env.tc_hooks);
                    FStarC_TypeChecker_Env.dsenv =
                      (e.FStarC_TypeChecker_Env.dsenv);
                    FStarC_TypeChecker_Env.nbe =
                      (e.FStarC_TypeChecker_Env.nbe);
                    FStarC_TypeChecker_Env.strict_args_tab =
                      (e.FStarC_TypeChecker_Env.strict_args_tab);
                    FStarC_TypeChecker_Env.erasable_types_tab =
                      (e.FStarC_TypeChecker_Env.erasable_types_tab);
                    FStarC_TypeChecker_Env.enable_defer_to_tac =
                      (e.FStarC_TypeChecker_Env.enable_defer_to_tac);
                    FStarC_TypeChecker_Env.unif_allow_ref_guards =
                      (e.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                    FStarC_TypeChecker_Env.erase_erasable_args =
                      (e.FStarC_TypeChecker_Env.erase_erasable_args);
                    FStarC_TypeChecker_Env.core_check =
                      (e.FStarC_TypeChecker_Env.core_check);
                    FStarC_TypeChecker_Env.missing_decl =
                      (e.FStarC_TypeChecker_Env.missing_decl)
                  } in
                let e2 =
                  {
                    FStarC_TypeChecker_Env.solver =
                      (e1.FStarC_TypeChecker_Env.solver);
                    FStarC_TypeChecker_Env.range =
                      (e1.FStarC_TypeChecker_Env.range);
                    FStarC_TypeChecker_Env.curmodule =
                      (e1.FStarC_TypeChecker_Env.curmodule);
                    FStarC_TypeChecker_Env.gamma =
                      (e1.FStarC_TypeChecker_Env.gamma);
                    FStarC_TypeChecker_Env.gamma_sig =
                      (e1.FStarC_TypeChecker_Env.gamma_sig);
                    FStarC_TypeChecker_Env.gamma_cache =
                      (e1.FStarC_TypeChecker_Env.gamma_cache);
                    FStarC_TypeChecker_Env.modules =
                      (e1.FStarC_TypeChecker_Env.modules);
                    FStarC_TypeChecker_Env.expected_typ =
                      (e1.FStarC_TypeChecker_Env.expected_typ);
                    FStarC_TypeChecker_Env.sigtab =
                      (e1.FStarC_TypeChecker_Env.sigtab);
                    FStarC_TypeChecker_Env.attrtab =
                      (e1.FStarC_TypeChecker_Env.attrtab);
                    FStarC_TypeChecker_Env.instantiate_imp =
                      (e1.FStarC_TypeChecker_Env.instantiate_imp);
                    FStarC_TypeChecker_Env.effects =
                      (e1.FStarC_TypeChecker_Env.effects);
                    FStarC_TypeChecker_Env.generalize =
                      (e1.FStarC_TypeChecker_Env.generalize);
                    FStarC_TypeChecker_Env.letrecs = [];
                    FStarC_TypeChecker_Env.top_level =
                      (e1.FStarC_TypeChecker_Env.top_level);
                    FStarC_TypeChecker_Env.check_uvars =
                      (e1.FStarC_TypeChecker_Env.check_uvars);
                    FStarC_TypeChecker_Env.use_eq_strict =
                      (e1.FStarC_TypeChecker_Env.use_eq_strict);
                    FStarC_TypeChecker_Env.is_iface =
                      (e1.FStarC_TypeChecker_Env.is_iface);
                    FStarC_TypeChecker_Env.admit =
                      (e1.FStarC_TypeChecker_Env.admit);
                    FStarC_TypeChecker_Env.lax_universes =
                      (e1.FStarC_TypeChecker_Env.lax_universes);
                    FStarC_TypeChecker_Env.phase1 =
                      (e1.FStarC_TypeChecker_Env.phase1);
                    FStarC_TypeChecker_Env.failhard =
                      (e1.FStarC_TypeChecker_Env.failhard);
                    FStarC_TypeChecker_Env.flychecking =
                      (e1.FStarC_TypeChecker_Env.flychecking);
                    FStarC_TypeChecker_Env.uvar_subtyping =
                      (e1.FStarC_TypeChecker_Env.uvar_subtyping);
                    FStarC_TypeChecker_Env.intactics =
                      (e1.FStarC_TypeChecker_Env.intactics);
                    FStarC_TypeChecker_Env.nocoerce =
                      (e1.FStarC_TypeChecker_Env.nocoerce);
                    FStarC_TypeChecker_Env.tc_term =
                      (e1.FStarC_TypeChecker_Env.tc_term);
                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                      (e1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                    FStarC_TypeChecker_Env.universe_of =
                      (e1.FStarC_TypeChecker_Env.universe_of);
                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                      =
                      (e1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                    FStarC_TypeChecker_Env.teq_nosmt_force =
                      (e1.FStarC_TypeChecker_Env.teq_nosmt_force);
                    FStarC_TypeChecker_Env.subtype_nosmt_force =
                      (e1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                    FStarC_TypeChecker_Env.qtbl_name_and_index =
                      (e1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                    FStarC_TypeChecker_Env.normalized_eff_names =
                      (e1.FStarC_TypeChecker_Env.normalized_eff_names);
                    FStarC_TypeChecker_Env.fv_delta_depths =
                      (e1.FStarC_TypeChecker_Env.fv_delta_depths);
                    FStarC_TypeChecker_Env.proof_ns =
                      (e1.FStarC_TypeChecker_Env.proof_ns);
                    FStarC_TypeChecker_Env.synth_hook =
                      (e1.FStarC_TypeChecker_Env.synth_hook);
                    FStarC_TypeChecker_Env.try_solve_implicits_hook =
                      (e1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                    FStarC_TypeChecker_Env.splice =
                      (e1.FStarC_TypeChecker_Env.splice);
                    FStarC_TypeChecker_Env.mpreprocess =
                      (e1.FStarC_TypeChecker_Env.mpreprocess);
                    FStarC_TypeChecker_Env.postprocess =
                      (e1.FStarC_TypeChecker_Env.postprocess);
                    FStarC_TypeChecker_Env.identifier_info =
                      (e1.FStarC_TypeChecker_Env.identifier_info);
                    FStarC_TypeChecker_Env.tc_hooks =
                      (e1.FStarC_TypeChecker_Env.tc_hooks);
                    FStarC_TypeChecker_Env.dsenv =
                      (e1.FStarC_TypeChecker_Env.dsenv);
                    FStarC_TypeChecker_Env.nbe =
                      (e1.FStarC_TypeChecker_Env.nbe);
                    FStarC_TypeChecker_Env.strict_args_tab =
                      (e1.FStarC_TypeChecker_Env.strict_args_tab);
                    FStarC_TypeChecker_Env.erasable_types_tab =
                      (e1.FStarC_TypeChecker_Env.erasable_types_tab);
                    FStarC_TypeChecker_Env.enable_defer_to_tac =
                      (e1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                    FStarC_TypeChecker_Env.unif_allow_ref_guards =
                      (e1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                    FStarC_TypeChecker_Env.erase_erasable_args =
                      (e1.FStarC_TypeChecker_Env.erase_erasable_args);
                    FStarC_TypeChecker_Env.core_check =
                      (e1.FStarC_TypeChecker_Env.core_check);
                    FStarC_TypeChecker_Env.missing_decl =
                      (e1.FStarC_TypeChecker_Env.missing_decl)
                  } in
                try
                  (fun uu___2 ->
                     match () with
                     | () ->
                         let uu___3 =
                           FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term e2 t in
                         (match uu___3 with
                          | (t1, lc, g) ->
                              ret
                                (t1, (lc.FStarC_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStarC_Errors.Error (uu___3, msg, uu___4, uu___5) ->
                    let uu___6 = tts e2 t in
                    let uu___7 =
                      let uu___8 = FStarC_TypeChecker_Env.all_binders e2 in
                      FStarC_Class_Show.show
                        (FStarC_Class_Show.show_list
                           FStarC_Syntax_Print.showable_binder) uu___8 in
                    let uu___8 = FStarC_Errors_Msg.rendermsg msg in
                    fail3 "Cannot type (2) %s in context (%s). Error = (%s)"
                      uu___6 uu___7 uu___8))
let (__tc_lax :
  env ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_Common.lcomp *
        FStarC_TypeChecker_Common.guard_t) FStarC_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu___ = bind () in
      uu___ FStarC_Tactics_Monad.get
        (fun ps ->
           FStarC_Tactics_Monad.mlog
             (fun uu___1 ->
                let uu___2 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
                let uu___3 =
                  let uu___4 = FStarC_TypeChecker_Env.all_binders e in
                  FStarC_Class_Show.show
                    (FStarC_Class_Show.show_list
                       FStarC_Syntax_Print.showable_binder) uu___4 in
                FStarC_Compiler_Util.print2 "Tac> __tc_lax(%s)(Context:%s)\n"
                  uu___2 uu___3)
             (fun uu___1 ->
                let e1 =
                  {
                    FStarC_TypeChecker_Env.solver =
                      (e.FStarC_TypeChecker_Env.solver);
                    FStarC_TypeChecker_Env.range =
                      (e.FStarC_TypeChecker_Env.range);
                    FStarC_TypeChecker_Env.curmodule =
                      (e.FStarC_TypeChecker_Env.curmodule);
                    FStarC_TypeChecker_Env.gamma =
                      (e.FStarC_TypeChecker_Env.gamma);
                    FStarC_TypeChecker_Env.gamma_sig =
                      (e.FStarC_TypeChecker_Env.gamma_sig);
                    FStarC_TypeChecker_Env.gamma_cache =
                      (e.FStarC_TypeChecker_Env.gamma_cache);
                    FStarC_TypeChecker_Env.modules =
                      (e.FStarC_TypeChecker_Env.modules);
                    FStarC_TypeChecker_Env.expected_typ =
                      (e.FStarC_TypeChecker_Env.expected_typ);
                    FStarC_TypeChecker_Env.sigtab =
                      (e.FStarC_TypeChecker_Env.sigtab);
                    FStarC_TypeChecker_Env.attrtab =
                      (e.FStarC_TypeChecker_Env.attrtab);
                    FStarC_TypeChecker_Env.instantiate_imp =
                      (e.FStarC_TypeChecker_Env.instantiate_imp);
                    FStarC_TypeChecker_Env.effects =
                      (e.FStarC_TypeChecker_Env.effects);
                    FStarC_TypeChecker_Env.generalize =
                      (e.FStarC_TypeChecker_Env.generalize);
                    FStarC_TypeChecker_Env.letrecs =
                      (e.FStarC_TypeChecker_Env.letrecs);
                    FStarC_TypeChecker_Env.top_level =
                      (e.FStarC_TypeChecker_Env.top_level);
                    FStarC_TypeChecker_Env.check_uvars =
                      (e.FStarC_TypeChecker_Env.check_uvars);
                    FStarC_TypeChecker_Env.use_eq_strict =
                      (e.FStarC_TypeChecker_Env.use_eq_strict);
                    FStarC_TypeChecker_Env.is_iface =
                      (e.FStarC_TypeChecker_Env.is_iface);
                    FStarC_TypeChecker_Env.admit =
                      (e.FStarC_TypeChecker_Env.admit);
                    FStarC_TypeChecker_Env.lax_universes =
                      (e.FStarC_TypeChecker_Env.lax_universes);
                    FStarC_TypeChecker_Env.phase1 =
                      (e.FStarC_TypeChecker_Env.phase1);
                    FStarC_TypeChecker_Env.failhard =
                      (e.FStarC_TypeChecker_Env.failhard);
                    FStarC_TypeChecker_Env.flychecking =
                      (e.FStarC_TypeChecker_Env.flychecking);
                    FStarC_TypeChecker_Env.uvar_subtyping = false;
                    FStarC_TypeChecker_Env.intactics =
                      (e.FStarC_TypeChecker_Env.intactics);
                    FStarC_TypeChecker_Env.nocoerce =
                      (e.FStarC_TypeChecker_Env.nocoerce);
                    FStarC_TypeChecker_Env.tc_term =
                      (e.FStarC_TypeChecker_Env.tc_term);
                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                      (e.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                    FStarC_TypeChecker_Env.universe_of =
                      (e.FStarC_TypeChecker_Env.universe_of);
                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                      =
                      (e.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                    FStarC_TypeChecker_Env.teq_nosmt_force =
                      (e.FStarC_TypeChecker_Env.teq_nosmt_force);
                    FStarC_TypeChecker_Env.subtype_nosmt_force =
                      (e.FStarC_TypeChecker_Env.subtype_nosmt_force);
                    FStarC_TypeChecker_Env.qtbl_name_and_index =
                      (e.FStarC_TypeChecker_Env.qtbl_name_and_index);
                    FStarC_TypeChecker_Env.normalized_eff_names =
                      (e.FStarC_TypeChecker_Env.normalized_eff_names);
                    FStarC_TypeChecker_Env.fv_delta_depths =
                      (e.FStarC_TypeChecker_Env.fv_delta_depths);
                    FStarC_TypeChecker_Env.proof_ns =
                      (e.FStarC_TypeChecker_Env.proof_ns);
                    FStarC_TypeChecker_Env.synth_hook =
                      (e.FStarC_TypeChecker_Env.synth_hook);
                    FStarC_TypeChecker_Env.try_solve_implicits_hook =
                      (e.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                    FStarC_TypeChecker_Env.splice =
                      (e.FStarC_TypeChecker_Env.splice);
                    FStarC_TypeChecker_Env.mpreprocess =
                      (e.FStarC_TypeChecker_Env.mpreprocess);
                    FStarC_TypeChecker_Env.postprocess =
                      (e.FStarC_TypeChecker_Env.postprocess);
                    FStarC_TypeChecker_Env.identifier_info =
                      (e.FStarC_TypeChecker_Env.identifier_info);
                    FStarC_TypeChecker_Env.tc_hooks =
                      (e.FStarC_TypeChecker_Env.tc_hooks);
                    FStarC_TypeChecker_Env.dsenv =
                      (e.FStarC_TypeChecker_Env.dsenv);
                    FStarC_TypeChecker_Env.nbe =
                      (e.FStarC_TypeChecker_Env.nbe);
                    FStarC_TypeChecker_Env.strict_args_tab =
                      (e.FStarC_TypeChecker_Env.strict_args_tab);
                    FStarC_TypeChecker_Env.erasable_types_tab =
                      (e.FStarC_TypeChecker_Env.erasable_types_tab);
                    FStarC_TypeChecker_Env.enable_defer_to_tac =
                      (e.FStarC_TypeChecker_Env.enable_defer_to_tac);
                    FStarC_TypeChecker_Env.unif_allow_ref_guards =
                      (e.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                    FStarC_TypeChecker_Env.erase_erasable_args =
                      (e.FStarC_TypeChecker_Env.erase_erasable_args);
                    FStarC_TypeChecker_Env.core_check =
                      (e.FStarC_TypeChecker_Env.core_check);
                    FStarC_TypeChecker_Env.missing_decl =
                      (e.FStarC_TypeChecker_Env.missing_decl)
                  } in
                let e2 =
                  {
                    FStarC_TypeChecker_Env.solver =
                      (e1.FStarC_TypeChecker_Env.solver);
                    FStarC_TypeChecker_Env.range =
                      (e1.FStarC_TypeChecker_Env.range);
                    FStarC_TypeChecker_Env.curmodule =
                      (e1.FStarC_TypeChecker_Env.curmodule);
                    FStarC_TypeChecker_Env.gamma =
                      (e1.FStarC_TypeChecker_Env.gamma);
                    FStarC_TypeChecker_Env.gamma_sig =
                      (e1.FStarC_TypeChecker_Env.gamma_sig);
                    FStarC_TypeChecker_Env.gamma_cache =
                      (e1.FStarC_TypeChecker_Env.gamma_cache);
                    FStarC_TypeChecker_Env.modules =
                      (e1.FStarC_TypeChecker_Env.modules);
                    FStarC_TypeChecker_Env.expected_typ =
                      (e1.FStarC_TypeChecker_Env.expected_typ);
                    FStarC_TypeChecker_Env.sigtab =
                      (e1.FStarC_TypeChecker_Env.sigtab);
                    FStarC_TypeChecker_Env.attrtab =
                      (e1.FStarC_TypeChecker_Env.attrtab);
                    FStarC_TypeChecker_Env.instantiate_imp =
                      (e1.FStarC_TypeChecker_Env.instantiate_imp);
                    FStarC_TypeChecker_Env.effects =
                      (e1.FStarC_TypeChecker_Env.effects);
                    FStarC_TypeChecker_Env.generalize =
                      (e1.FStarC_TypeChecker_Env.generalize);
                    FStarC_TypeChecker_Env.letrecs =
                      (e1.FStarC_TypeChecker_Env.letrecs);
                    FStarC_TypeChecker_Env.top_level =
                      (e1.FStarC_TypeChecker_Env.top_level);
                    FStarC_TypeChecker_Env.check_uvars =
                      (e1.FStarC_TypeChecker_Env.check_uvars);
                    FStarC_TypeChecker_Env.use_eq_strict =
                      (e1.FStarC_TypeChecker_Env.use_eq_strict);
                    FStarC_TypeChecker_Env.is_iface =
                      (e1.FStarC_TypeChecker_Env.is_iface);
                    FStarC_TypeChecker_Env.admit = true;
                    FStarC_TypeChecker_Env.lax_universes =
                      (e1.FStarC_TypeChecker_Env.lax_universes);
                    FStarC_TypeChecker_Env.phase1 =
                      (e1.FStarC_TypeChecker_Env.phase1);
                    FStarC_TypeChecker_Env.failhard =
                      (e1.FStarC_TypeChecker_Env.failhard);
                    FStarC_TypeChecker_Env.flychecking =
                      (e1.FStarC_TypeChecker_Env.flychecking);
                    FStarC_TypeChecker_Env.uvar_subtyping =
                      (e1.FStarC_TypeChecker_Env.uvar_subtyping);
                    FStarC_TypeChecker_Env.intactics =
                      (e1.FStarC_TypeChecker_Env.intactics);
                    FStarC_TypeChecker_Env.nocoerce =
                      (e1.FStarC_TypeChecker_Env.nocoerce);
                    FStarC_TypeChecker_Env.tc_term =
                      (e1.FStarC_TypeChecker_Env.tc_term);
                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                      (e1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                    FStarC_TypeChecker_Env.universe_of =
                      (e1.FStarC_TypeChecker_Env.universe_of);
                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                      =
                      (e1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                    FStarC_TypeChecker_Env.teq_nosmt_force =
                      (e1.FStarC_TypeChecker_Env.teq_nosmt_force);
                    FStarC_TypeChecker_Env.subtype_nosmt_force =
                      (e1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                    FStarC_TypeChecker_Env.qtbl_name_and_index =
                      (e1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                    FStarC_TypeChecker_Env.normalized_eff_names =
                      (e1.FStarC_TypeChecker_Env.normalized_eff_names);
                    FStarC_TypeChecker_Env.fv_delta_depths =
                      (e1.FStarC_TypeChecker_Env.fv_delta_depths);
                    FStarC_TypeChecker_Env.proof_ns =
                      (e1.FStarC_TypeChecker_Env.proof_ns);
                    FStarC_TypeChecker_Env.synth_hook =
                      (e1.FStarC_TypeChecker_Env.synth_hook);
                    FStarC_TypeChecker_Env.try_solve_implicits_hook =
                      (e1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                    FStarC_TypeChecker_Env.splice =
                      (e1.FStarC_TypeChecker_Env.splice);
                    FStarC_TypeChecker_Env.mpreprocess =
                      (e1.FStarC_TypeChecker_Env.mpreprocess);
                    FStarC_TypeChecker_Env.postprocess =
                      (e1.FStarC_TypeChecker_Env.postprocess);
                    FStarC_TypeChecker_Env.identifier_info =
                      (e1.FStarC_TypeChecker_Env.identifier_info);
                    FStarC_TypeChecker_Env.tc_hooks =
                      (e1.FStarC_TypeChecker_Env.tc_hooks);
                    FStarC_TypeChecker_Env.dsenv =
                      (e1.FStarC_TypeChecker_Env.dsenv);
                    FStarC_TypeChecker_Env.nbe =
                      (e1.FStarC_TypeChecker_Env.nbe);
                    FStarC_TypeChecker_Env.strict_args_tab =
                      (e1.FStarC_TypeChecker_Env.strict_args_tab);
                    FStarC_TypeChecker_Env.erasable_types_tab =
                      (e1.FStarC_TypeChecker_Env.erasable_types_tab);
                    FStarC_TypeChecker_Env.enable_defer_to_tac =
                      (e1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                    FStarC_TypeChecker_Env.unif_allow_ref_guards =
                      (e1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                    FStarC_TypeChecker_Env.erase_erasable_args =
                      (e1.FStarC_TypeChecker_Env.erase_erasable_args);
                    FStarC_TypeChecker_Env.core_check =
                      (e1.FStarC_TypeChecker_Env.core_check);
                    FStarC_TypeChecker_Env.missing_decl =
                      (e1.FStarC_TypeChecker_Env.missing_decl)
                  } in
                let e3 =
                  {
                    FStarC_TypeChecker_Env.solver =
                      (e2.FStarC_TypeChecker_Env.solver);
                    FStarC_TypeChecker_Env.range =
                      (e2.FStarC_TypeChecker_Env.range);
                    FStarC_TypeChecker_Env.curmodule =
                      (e2.FStarC_TypeChecker_Env.curmodule);
                    FStarC_TypeChecker_Env.gamma =
                      (e2.FStarC_TypeChecker_Env.gamma);
                    FStarC_TypeChecker_Env.gamma_sig =
                      (e2.FStarC_TypeChecker_Env.gamma_sig);
                    FStarC_TypeChecker_Env.gamma_cache =
                      (e2.FStarC_TypeChecker_Env.gamma_cache);
                    FStarC_TypeChecker_Env.modules =
                      (e2.FStarC_TypeChecker_Env.modules);
                    FStarC_TypeChecker_Env.expected_typ =
                      (e2.FStarC_TypeChecker_Env.expected_typ);
                    FStarC_TypeChecker_Env.sigtab =
                      (e2.FStarC_TypeChecker_Env.sigtab);
                    FStarC_TypeChecker_Env.attrtab =
                      (e2.FStarC_TypeChecker_Env.attrtab);
                    FStarC_TypeChecker_Env.instantiate_imp =
                      (e2.FStarC_TypeChecker_Env.instantiate_imp);
                    FStarC_TypeChecker_Env.effects =
                      (e2.FStarC_TypeChecker_Env.effects);
                    FStarC_TypeChecker_Env.generalize =
                      (e2.FStarC_TypeChecker_Env.generalize);
                    FStarC_TypeChecker_Env.letrecs = [];
                    FStarC_TypeChecker_Env.top_level =
                      (e2.FStarC_TypeChecker_Env.top_level);
                    FStarC_TypeChecker_Env.check_uvars =
                      (e2.FStarC_TypeChecker_Env.check_uvars);
                    FStarC_TypeChecker_Env.use_eq_strict =
                      (e2.FStarC_TypeChecker_Env.use_eq_strict);
                    FStarC_TypeChecker_Env.is_iface =
                      (e2.FStarC_TypeChecker_Env.is_iface);
                    FStarC_TypeChecker_Env.admit =
                      (e2.FStarC_TypeChecker_Env.admit);
                    FStarC_TypeChecker_Env.lax_universes =
                      (e2.FStarC_TypeChecker_Env.lax_universes);
                    FStarC_TypeChecker_Env.phase1 =
                      (e2.FStarC_TypeChecker_Env.phase1);
                    FStarC_TypeChecker_Env.failhard =
                      (e2.FStarC_TypeChecker_Env.failhard);
                    FStarC_TypeChecker_Env.flychecking =
                      (e2.FStarC_TypeChecker_Env.flychecking);
                    FStarC_TypeChecker_Env.uvar_subtyping =
                      (e2.FStarC_TypeChecker_Env.uvar_subtyping);
                    FStarC_TypeChecker_Env.intactics =
                      (e2.FStarC_TypeChecker_Env.intactics);
                    FStarC_TypeChecker_Env.nocoerce =
                      (e2.FStarC_TypeChecker_Env.nocoerce);
                    FStarC_TypeChecker_Env.tc_term =
                      (e2.FStarC_TypeChecker_Env.tc_term);
                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                      (e2.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                    FStarC_TypeChecker_Env.universe_of =
                      (e2.FStarC_TypeChecker_Env.universe_of);
                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                      =
                      (e2.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                    FStarC_TypeChecker_Env.teq_nosmt_force =
                      (e2.FStarC_TypeChecker_Env.teq_nosmt_force);
                    FStarC_TypeChecker_Env.subtype_nosmt_force =
                      (e2.FStarC_TypeChecker_Env.subtype_nosmt_force);
                    FStarC_TypeChecker_Env.qtbl_name_and_index =
                      (e2.FStarC_TypeChecker_Env.qtbl_name_and_index);
                    FStarC_TypeChecker_Env.normalized_eff_names =
                      (e2.FStarC_TypeChecker_Env.normalized_eff_names);
                    FStarC_TypeChecker_Env.fv_delta_depths =
                      (e2.FStarC_TypeChecker_Env.fv_delta_depths);
                    FStarC_TypeChecker_Env.proof_ns =
                      (e2.FStarC_TypeChecker_Env.proof_ns);
                    FStarC_TypeChecker_Env.synth_hook =
                      (e2.FStarC_TypeChecker_Env.synth_hook);
                    FStarC_TypeChecker_Env.try_solve_implicits_hook =
                      (e2.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                    FStarC_TypeChecker_Env.splice =
                      (e2.FStarC_TypeChecker_Env.splice);
                    FStarC_TypeChecker_Env.mpreprocess =
                      (e2.FStarC_TypeChecker_Env.mpreprocess);
                    FStarC_TypeChecker_Env.postprocess =
                      (e2.FStarC_TypeChecker_Env.postprocess);
                    FStarC_TypeChecker_Env.identifier_info =
                      (e2.FStarC_TypeChecker_Env.identifier_info);
                    FStarC_TypeChecker_Env.tc_hooks =
                      (e2.FStarC_TypeChecker_Env.tc_hooks);
                    FStarC_TypeChecker_Env.dsenv =
                      (e2.FStarC_TypeChecker_Env.dsenv);
                    FStarC_TypeChecker_Env.nbe =
                      (e2.FStarC_TypeChecker_Env.nbe);
                    FStarC_TypeChecker_Env.strict_args_tab =
                      (e2.FStarC_TypeChecker_Env.strict_args_tab);
                    FStarC_TypeChecker_Env.erasable_types_tab =
                      (e2.FStarC_TypeChecker_Env.erasable_types_tab);
                    FStarC_TypeChecker_Env.enable_defer_to_tac =
                      (e2.FStarC_TypeChecker_Env.enable_defer_to_tac);
                    FStarC_TypeChecker_Env.unif_allow_ref_guards =
                      (e2.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                    FStarC_TypeChecker_Env.erase_erasable_args =
                      (e2.FStarC_TypeChecker_Env.erase_erasable_args);
                    FStarC_TypeChecker_Env.core_check =
                      (e2.FStarC_TypeChecker_Env.core_check);
                    FStarC_TypeChecker_Env.missing_decl =
                      (e2.FStarC_TypeChecker_Env.missing_decl)
                  } in
                try
                  (fun uu___2 ->
                     match () with
                     | () ->
                         let uu___3 = FStarC_TypeChecker_TcTerm.tc_term e3 t in
                         ret uu___3) ()
                with
                | FStarC_Errors.Error (uu___3, msg, uu___4, uu___5) ->
                    let uu___6 = tts e3 t in
                    let uu___7 =
                      let uu___8 = FStarC_TypeChecker_Env.all_binders e3 in
                      FStarC_Class_Show.show
                        (FStarC_Class_Show.show_list
                           FStarC_Syntax_Print.showable_binder) uu___8 in
                    let uu___8 = FStarC_Errors_Msg.rendermsg msg in
                    fail3 "Cannot type (3) %s in context (%s). Error = (%s)"
                      uu___6 uu___7 uu___8))
let (tcc :
  env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.comp FStarC_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu___ =
        let uu___1 = __tc_lax e t in
        let uu___2 = bind () in
        uu___2 uu___1
          (fun uu___3 ->
             match uu___3 with
             | (uu___4, lc, uu___5) ->
                 let uu___6 =
                   let uu___7 = FStarC_TypeChecker_Common.lcomp_comp lc in
                   FStar_Pervasives_Native.fst uu___7 in
                 ret uu___6) in
      FStarC_Tactics_Monad.wrap_err "tcc" uu___
let (tc :
  env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.typ FStarC_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu___ =
        let uu___1 = tcc e t in
        let uu___2 = bind () in
        uu___2 uu___1 (fun c -> ret (FStarC_Syntax_Util.comp_result c)) in
      FStarC_Tactics_Monad.wrap_err "tc" uu___
let divide :
  'a 'b .
    FStarC_BigInt.t ->
      'a FStarC_Tactics_Monad.tac ->
        'b FStarC_Tactics_Monad.tac -> ('a * 'b) FStarC_Tactics_Monad.tac
  =
  fun n ->
    fun l ->
      fun r ->
        let uu___ = bind () in
        uu___ FStarC_Tactics_Monad.get
          (fun p ->
             let uu___1 =
               try
                 (fun uu___2 ->
                    match () with
                    | () ->
                        let uu___3 =
                          let uu___4 = FStarC_BigInt.to_int_fs n in
                          FStarC_Compiler_List.splitAt uu___4
                            p.FStarC_Tactics_Types.goals in
                        ret uu___3) ()
               with
               | uu___2 ->
                   FStarC_Tactics_Monad.fail "divide: not enough goals" in
             let uu___2 = bind () in
             uu___2 uu___1
               (fun uu___3 ->
                  match uu___3 with
                  | (lgs, rgs) ->
                      let lp =
                        {
                          FStarC_Tactics_Types.main_context =
                            (p.FStarC_Tactics_Types.main_context);
                          FStarC_Tactics_Types.all_implicits =
                            (p.FStarC_Tactics_Types.all_implicits);
                          FStarC_Tactics_Types.goals = lgs;
                          FStarC_Tactics_Types.smt_goals = [];
                          FStarC_Tactics_Types.depth =
                            (p.FStarC_Tactics_Types.depth);
                          FStarC_Tactics_Types.__dump =
                            (p.FStarC_Tactics_Types.__dump);
                          FStarC_Tactics_Types.psc =
                            (p.FStarC_Tactics_Types.psc);
                          FStarC_Tactics_Types.entry_range =
                            (p.FStarC_Tactics_Types.entry_range);
                          FStarC_Tactics_Types.guard_policy =
                            (p.FStarC_Tactics_Types.guard_policy);
                          FStarC_Tactics_Types.freshness =
                            (p.FStarC_Tactics_Types.freshness);
                          FStarC_Tactics_Types.tac_verb_dbg =
                            (p.FStarC_Tactics_Types.tac_verb_dbg);
                          FStarC_Tactics_Types.local_state =
                            (p.FStarC_Tactics_Types.local_state);
                          FStarC_Tactics_Types.urgency =
                            (p.FStarC_Tactics_Types.urgency);
                          FStarC_Tactics_Types.dump_on_failure =
                            (p.FStarC_Tactics_Types.dump_on_failure)
                        } in
                      let uu___4 = FStarC_Tactics_Monad.set lp in
                      let uu___5 = bind () in
                      uu___5 uu___4
                        (fun uu___6 ->
                           let uu___7 = bind () in
                           uu___7 l
                             (fun a1 ->
                                let uu___8 = bind () in
                                uu___8 FStarC_Tactics_Monad.get
                                  (fun lp' ->
                                     let rp =
                                       {
                                         FStarC_Tactics_Types.main_context =
                                           (lp'.FStarC_Tactics_Types.main_context);
                                         FStarC_Tactics_Types.all_implicits =
                                           (lp'.FStarC_Tactics_Types.all_implicits);
                                         FStarC_Tactics_Types.goals = rgs;
                                         FStarC_Tactics_Types.smt_goals = [];
                                         FStarC_Tactics_Types.depth =
                                           (lp'.FStarC_Tactics_Types.depth);
                                         FStarC_Tactics_Types.__dump =
                                           (lp'.FStarC_Tactics_Types.__dump);
                                         FStarC_Tactics_Types.psc =
                                           (lp'.FStarC_Tactics_Types.psc);
                                         FStarC_Tactics_Types.entry_range =
                                           (lp'.FStarC_Tactics_Types.entry_range);
                                         FStarC_Tactics_Types.guard_policy =
                                           (lp'.FStarC_Tactics_Types.guard_policy);
                                         FStarC_Tactics_Types.freshness =
                                           (lp'.FStarC_Tactics_Types.freshness);
                                         FStarC_Tactics_Types.tac_verb_dbg =
                                           (lp'.FStarC_Tactics_Types.tac_verb_dbg);
                                         FStarC_Tactics_Types.local_state =
                                           (lp'.FStarC_Tactics_Types.local_state);
                                         FStarC_Tactics_Types.urgency =
                                           (lp'.FStarC_Tactics_Types.urgency);
                                         FStarC_Tactics_Types.dump_on_failure
                                           =
                                           (lp'.FStarC_Tactics_Types.dump_on_failure)
                                       } in
                                     let uu___9 = FStarC_Tactics_Monad.set rp in
                                     let uu___10 = bind () in
                                     uu___10 uu___9
                                       (fun uu___11 ->
                                          let uu___12 = bind () in
                                          uu___12 r
                                            (fun b1 ->
                                               let uu___13 = bind () in
                                               uu___13
                                                 FStarC_Tactics_Monad.get
                                                 (fun rp' ->
                                                    let p' =
                                                      {
                                                        FStarC_Tactics_Types.main_context
                                                          =
                                                          (rp'.FStarC_Tactics_Types.main_context);
                                                        FStarC_Tactics_Types.all_implicits
                                                          =
                                                          (rp'.FStarC_Tactics_Types.all_implicits);
                                                        FStarC_Tactics_Types.goals
                                                          =
                                                          (FStarC_Compiler_List.op_At
                                                             lp'.FStarC_Tactics_Types.goals
                                                             rp'.FStarC_Tactics_Types.goals);
                                                        FStarC_Tactics_Types.smt_goals
                                                          =
                                                          (FStarC_Compiler_List.op_At
                                                             lp'.FStarC_Tactics_Types.smt_goals
                                                             (FStarC_Compiler_List.op_At
                                                                rp'.FStarC_Tactics_Types.smt_goals
                                                                p.FStarC_Tactics_Types.smt_goals));
                                                        FStarC_Tactics_Types.depth
                                                          =
                                                          (rp'.FStarC_Tactics_Types.depth);
                                                        FStarC_Tactics_Types.__dump
                                                          =
                                                          (rp'.FStarC_Tactics_Types.__dump);
                                                        FStarC_Tactics_Types.psc
                                                          =
                                                          (rp'.FStarC_Tactics_Types.psc);
                                                        FStarC_Tactics_Types.entry_range
                                                          =
                                                          (rp'.FStarC_Tactics_Types.entry_range);
                                                        FStarC_Tactics_Types.guard_policy
                                                          =
                                                          (rp'.FStarC_Tactics_Types.guard_policy);
                                                        FStarC_Tactics_Types.freshness
                                                          =
                                                          (rp'.FStarC_Tactics_Types.freshness);
                                                        FStarC_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (rp'.FStarC_Tactics_Types.tac_verb_dbg);
                                                        FStarC_Tactics_Types.local_state
                                                          =
                                                          (rp'.FStarC_Tactics_Types.local_state);
                                                        FStarC_Tactics_Types.urgency
                                                          =
                                                          (rp'.FStarC_Tactics_Types.urgency);
                                                        FStarC_Tactics_Types.dump_on_failure
                                                          =
                                                          (rp'.FStarC_Tactics_Types.dump_on_failure)
                                                      } in
                                                    let uu___14 =
                                                      FStarC_Tactics_Monad.set
                                                        p' in
                                                    let uu___15 = bind () in
                                                    uu___15 uu___14
                                                      (fun uu___16 ->
                                                         let uu___17 =
                                                           bind () in
                                                         uu___17
                                                           FStarC_Tactics_Monad.remove_solved_goals
                                                           (fun uu___18 ->
                                                              ret (a1, b1)))))))))))
let focus : 'a . 'a FStarC_Tactics_Monad.tac -> 'a FStarC_Tactics_Monad.tac =
  fun f ->
    let uu___ = divide FStarC_BigInt.one f idtac in
    let uu___1 = bind () in
    uu___1 uu___ (fun uu___2 -> match uu___2 with | (a1, ()) -> ret a1)
let rec map :
  'a . 'a FStarC_Tactics_Monad.tac -> 'a Prims.list FStarC_Tactics_Monad.tac
  =
  fun tau ->
    let uu___ = bind () in
    uu___ FStarC_Tactics_Monad.get
      (fun p ->
         match p.FStarC_Tactics_Types.goals with
         | [] -> ret []
         | uu___1::uu___2 ->
             let uu___3 =
               let uu___4 = map tau in divide FStarC_BigInt.one tau uu___4 in
             let uu___4 = bind () in
             uu___4 uu___3
               (fun uu___5 -> match uu___5 with | (h, t) -> ret (h :: t)))
let (seq :
  unit FStarC_Tactics_Monad.tac ->
    unit FStarC_Tactics_Monad.tac -> unit FStarC_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let uu___ =
        let uu___1 = bind () in
        uu___1 t1
          (fun uu___2 ->
             let uu___3 = map t2 in
             let uu___4 = bind () in uu___4 uu___3 (fun uu___5 -> ret ())) in
      focus uu___
let (should_check_goal_uvar :
  FStarC_Tactics_Types.goal -> FStarC_Syntax_Syntax.should_check_uvar) =
  fun g ->
    FStarC_Syntax_Util.ctx_uvar_should_check
      g.FStarC_Tactics_Types.goal_ctx_uvar
let (goal_typedness_deps :
  FStarC_Tactics_Types.goal -> FStarC_Syntax_Syntax.ctx_uvar Prims.list) =
  fun g ->
    FStarC_Syntax_Util.ctx_uvar_typedness_deps
      g.FStarC_Tactics_Types.goal_ctx_uvar
let (bnorm_and_replace :
  FStarC_Tactics_Types.goal -> unit FStarC_Tactics_Monad.tac) =
  fun g -> let uu___ = bnorm_goal g in FStarC_Tactics_Monad.replace_cur uu___
let (arrow_one :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_TypeChecker_Env.env * FStarC_Syntax_Syntax.binder *
        FStarC_Syntax_Syntax.comp) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun t ->
      let uu___ = FStarC_Syntax_Util.arrow_one_ln t in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (b, c) ->
          let uu___1 =
            FStarC_TypeChecker_Core.open_binders_in_comp env1 [b] c in
          (match uu___1 with
           | (env2, b1::[], c1) ->
               FStar_Pervasives_Native.Some (env2, b1, c1))
let (intro : unit -> FStarC_Syntax_Syntax.binder FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      Obj.magic
        (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
           (Obj.magic FStarC_Tactics_Monad.cur_goal)
           (fun uu___2 ->
              (fun goal ->
                 let goal = Obj.magic goal in
                 let uu___2 =
                   let uu___3 = FStarC_Tactics_Types.goal_env goal in
                   let uu___4 =
                     let uu___5 = FStarC_Tactics_Types.goal_env goal in
                     let uu___6 = FStarC_Tactics_Types.goal_type goal in
                     whnf uu___5 uu___6 in
                   arrow_one uu___3 uu___4 in
                 match uu___2 with
                 | FStar_Pervasives_Native.Some (env', b, c) ->
                     Obj.magic
                       (Obj.repr
                          (let uu___3 =
                             let uu___4 = FStarC_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu___4 in
                           if uu___3
                           then
                             Obj.repr
                               (FStarC_Tactics_Monad.fail
                                  "Codomain is effectful")
                           else
                             Obj.repr
                               (let typ' = FStarC_Syntax_Util.comp_result c in
                                let uu___5 =
                                  let uu___6 =
                                    let uu___7 = should_check_goal_uvar goal in
                                    FStar_Pervasives_Native.Some uu___7 in
                                  let uu___7 = goal_typedness_deps goal in
                                  FStarC_Tactics_Monad.new_uvar "intro" env'
                                    typ' uu___6 uu___7 (rangeof goal) in
                                FStarC_Class_Monad.op_let_Bang
                                  FStarC_Tactics_Monad.monad_tac () ()
                                  (Obj.magic uu___5)
                                  (fun uu___6 ->
                                     (fun uu___6 ->
                                        let uu___6 = Obj.magic uu___6 in
                                        match uu___6 with
                                        | (body, ctx_uvar) ->
                                            let sol =
                                              let uu___7 =
                                                let uu___8 =
                                                  FStarC_Syntax_Util.residual_comp_of_comp
                                                    c in
                                                FStar_Pervasives_Native.Some
                                                  uu___8 in
                                              FStarC_Syntax_Util.abs 
                                                [b] body uu___7 in
                                            let uu___7 =
                                              set_solution goal sol in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_let_Bang
                                                 FStarC_Tactics_Monad.monad_tac
                                                 () () uu___7
                                                 (fun uu___8 ->
                                                    (fun uu___8 ->
                                                       let uu___8 =
                                                         Obj.magic uu___8 in
                                                       let g =
                                                         FStarC_Tactics_Types.mk_goal
                                                           env' ctx_uvar
                                                           goal.FStarC_Tactics_Types.opts
                                                           goal.FStarC_Tactics_Types.is_guard
                                                           goal.FStarC_Tactics_Types.label in
                                                       let uu___9 =
                                                         bnorm_and_replace g in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.op_let_Bang
                                                            FStarC_Tactics_Monad.monad_tac
                                                            () () uu___9
                                                            (fun uu___10 ->
                                                               (fun uu___10
                                                                  ->
                                                                  let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    uu___10 in
                                                                  Obj.magic
                                                                    (
                                                                    ret b))
                                                                 uu___10)))
                                                      uu___8))) uu___6))))
                 | FStar_Pervasives_Native.None ->
                     Obj.magic
                       (Obj.repr
                          (let uu___3 =
                             let uu___4 = FStarC_Tactics_Types.goal_env goal in
                             let uu___5 = FStarC_Tactics_Types.goal_type goal in
                             tts uu___4 uu___5 in
                           fail1 "goal is not an arrow (%s)" uu___3))) uu___2)) in
    FStarC_Tactics_Monad.wrap_err "intro" uu___1
let (intro_rec :
  unit ->
    (FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.binder)
      FStarC_Tactics_Monad.tac)
  =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
            (Obj.magic FStarC_Tactics_Monad.cur_goal)
            (fun uu___1 ->
               (fun goal ->
                  let goal = Obj.magic goal in
                  FStarC_Compiler_Util.print_string
                    "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
                  FStarC_Compiler_Util.print_string
                    "WARNING (intro_rec): proceed at your own risk...\n";
                  (let uu___3 =
                     let uu___4 = FStarC_Tactics_Types.goal_env goal in
                     let uu___5 =
                       let uu___6 = FStarC_Tactics_Types.goal_env goal in
                       let uu___7 = FStarC_Tactics_Types.goal_type goal in
                       whnf uu___6 uu___7 in
                     arrow_one uu___4 uu___5 in
                   match uu___3 with
                   | FStar_Pervasives_Native.Some (env', b, c) ->
                       Obj.magic
                         (Obj.repr
                            (let uu___4 =
                               let uu___5 =
                                 FStarC_Syntax_Util.is_total_comp c in
                               Prims.op_Negation uu___5 in
                             if uu___4
                             then
                               Obj.repr
                                 (FStarC_Tactics_Monad.fail
                                    "Codomain is effectful")
                             else
                               Obj.repr
                                 (let bv =
                                    let uu___6 =
                                      FStarC_Tactics_Types.goal_type goal in
                                    FStarC_Syntax_Syntax.gen_bv "__recf"
                                      FStar_Pervasives_Native.None uu___6 in
                                  let uu___6 =
                                    let uu___7 =
                                      let uu___8 =
                                        should_check_goal_uvar goal in
                                      FStar_Pervasives_Native.Some uu___8 in
                                    let uu___8 = goal_typedness_deps goal in
                                    FStarC_Tactics_Monad.new_uvar "intro_rec"
                                      env' (FStarC_Syntax_Util.comp_result c)
                                      uu___7 uu___8 (rangeof goal) in
                                  FStarC_Class_Monad.op_let_Bang
                                    FStarC_Tactics_Monad.monad_tac () ()
                                    (Obj.magic uu___6)
                                    (fun uu___7 ->
                                       (fun uu___7 ->
                                          let uu___7 = Obj.magic uu___7 in
                                          match uu___7 with
                                          | (u, ctx_uvar_u) ->
                                              let lb =
                                                let uu___8 =
                                                  FStarC_Tactics_Types.goal_type
                                                    goal in
                                                let uu___9 =
                                                  FStarC_Syntax_Util.abs 
                                                    [b] u
                                                    FStar_Pervasives_Native.None in
                                                FStarC_Syntax_Util.mk_letbinding
                                                  (FStar_Pervasives.Inl bv)
                                                  [] uu___8
                                                  FStarC_Parser_Const.effect_Tot_lid
                                                  uu___9 []
                                                  FStarC_Compiler_Range_Type.dummyRange in
                                              let body =
                                                FStarC_Syntax_Syntax.bv_to_name
                                                  bv in
                                              let uu___8 =
                                                FStarC_Syntax_Subst.close_let_rec
                                                  [lb] body in
                                              (match uu___8 with
                                               | (lbs, body1) ->
                                                   let tm =
                                                     let uu___9 =
                                                       let uu___10 =
                                                         FStarC_Tactics_Types.goal_witness
                                                           goal in
                                                       uu___10.FStarC_Syntax_Syntax.pos in
                                                     FStarC_Syntax_Syntax.mk
                                                       (FStarC_Syntax_Syntax.Tm_let
                                                          {
                                                            FStarC_Syntax_Syntax.lbs
                                                              = (true, lbs);
                                                            FStarC_Syntax_Syntax.body1
                                                              = body1
                                                          }) uu___9 in
                                                   let uu___9 =
                                                     set_solution goal tm in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_let_Bang
                                                        FStarC_Tactics_Monad.monad_tac
                                                        () () uu___9
                                                        (fun uu___10 ->
                                                           (fun uu___10 ->
                                                              let uu___10 =
                                                                Obj.magic
                                                                  uu___10 in
                                                              let uu___11 =
                                                                bnorm_and_replace
                                                                  {
                                                                    FStarC_Tactics_Types.goal_main_env
                                                                    =
                                                                    (goal.FStarC_Tactics_Types.goal_main_env);
                                                                    FStarC_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar_u;
                                                                    FStarC_Tactics_Types.opts
                                                                    =
                                                                    (goal.FStarC_Tactics_Types.opts);
                                                                    FStarC_Tactics_Types.is_guard
                                                                    =
                                                                    (goal.FStarC_Tactics_Types.is_guard);
                                                                    FStarC_Tactics_Types.label
                                                                    =
                                                                    (goal.FStarC_Tactics_Types.label)
                                                                  } in
                                                              Obj.magic
                                                                (FStarC_Class_Monad.op_let_Bang
                                                                   FStarC_Tactics_Monad.monad_tac
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
                                                                    FStarC_Syntax_Syntax.mk_binder
                                                                    bv in
                                                                    (uu___14,
                                                                    b) in
                                                                    Obj.magic
                                                                    (ret
                                                                    uu___13))
                                                                    uu___12)))
                                                             uu___10))))
                                         uu___7))))
                   | FStar_Pervasives_Native.None ->
                       Obj.magic
                         (Obj.repr
                            (let uu___4 =
                               let uu___5 =
                                 FStarC_Tactics_Types.goal_env goal in
                               let uu___6 =
                                 FStarC_Tactics_Types.goal_type goal in
                               tts uu___5 uu___6 in
                             fail1 "intro_rec: goal is not an arrow (%s)"
                               uu___4)))) uu___1))) uu___
let (norm :
  FStar_Pervasives.norm_step Prims.list -> unit FStarC_Tactics_Monad.tac) =
  fun s ->
    FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
      (Obj.magic FStarC_Tactics_Monad.cur_goal)
      (fun uu___ ->
         (fun goal ->
            let goal = Obj.magic goal in
            let uu___ =
              FStarC_Tactics_Monad.if_verbose
                (fun uu___1 ->
                   let uu___2 =
                     let uu___3 = FStarC_Tactics_Types.goal_witness goal in
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                       uu___3 in
                   FStarC_Compiler_Util.print1 "norm: witness = %s\n" uu___2) in
            Obj.magic
              (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac
                 () () uu___
                 (fun uu___1 ->
                    (fun uu___1 ->
                       let uu___1 = Obj.magic uu___1 in
                       let steps =
                         let uu___2 =
                           FStarC_TypeChecker_Cfg.translate_norm_steps s in
                         FStarC_Compiler_List.op_At
                           [FStarC_TypeChecker_Env.Reify;
                           FStarC_TypeChecker_Env.DontUnfoldAttr
                             [FStarC_Parser_Const.tac_opaque_attr]] uu___2 in
                       let t =
                         let uu___2 = FStarC_Tactics_Types.goal_env goal in
                         let uu___3 = FStarC_Tactics_Types.goal_type goal in
                         normalize steps uu___2 uu___3 in
                       let uu___2 = goal_with_type goal t in
                       Obj.magic (FStarC_Tactics_Monad.replace_cur uu___2))
                      uu___1))) uu___)
let (norm_term_env :
  env ->
    FStar_Pervasives.norm_step Prims.list ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.term FStarC_Tactics_Monad.tac)
  =
  fun e ->
    fun s ->
      fun t ->
        let uu___ =
          Obj.magic
            (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac ()
               () (Obj.magic FStarC_Tactics_Monad.get)
               (fun uu___1 ->
                  (fun ps ->
                     let ps = Obj.magic ps in
                     let uu___1 =
                       FStarC_Tactics_Monad.if_verbose
                         (fun uu___2 ->
                            let uu___3 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_term t in
                            FStarC_Compiler_Util.print1
                              "norm_term_env: t = %s\n" uu___3) in
                     Obj.magic
                       (FStarC_Class_Monad.op_let_Bang
                          FStarC_Tactics_Monad.monad_tac () () uu___1
                          (fun uu___2 ->
                             (fun uu___2 ->
                                let uu___2 = Obj.magic uu___2 in
                                let uu___3 = __tc_lax e t in
                                Obj.magic
                                  (FStarC_Class_Monad.op_let_Bang
                                     FStarC_Tactics_Monad.monad_tac () ()
                                     (Obj.magic uu___3)
                                     (fun uu___4 ->
                                        (fun uu___4 ->
                                           let uu___4 = Obj.magic uu___4 in
                                           match uu___4 with
                                           | (t1, uu___5, uu___6) ->
                                               let steps =
                                                 let uu___7 =
                                                   FStarC_TypeChecker_Cfg.translate_norm_steps
                                                     s in
                                                 FStarC_Compiler_List.op_At
                                                   [FStarC_TypeChecker_Env.Reify;
                                                   FStarC_TypeChecker_Env.DontUnfoldAttr
                                                     [FStarC_Parser_Const.tac_opaque_attr]]
                                                   uu___7 in
                                               let t2 =
                                                 normalize steps
                                                   ps.FStarC_Tactics_Types.main_context
                                                   t1 in
                                               let uu___7 =
                                                 FStarC_Tactics_Monad.if_verbose
                                                   (fun uu___8 ->
                                                      let uu___9 =
                                                        FStarC_Class_Show.show
                                                          FStarC_Syntax_Print.showable_term
                                                          t2 in
                                                      FStarC_Compiler_Util.print1
                                                        "norm_term_env: t' = %s\n"
                                                        uu___9) in
                                               Obj.magic
                                                 (FStarC_Class_Monad.op_let_Bang
                                                    FStarC_Tactics_Monad.monad_tac
                                                    () () uu___7
                                                    (fun uu___8 ->
                                                       (fun uu___8 ->
                                                          let uu___8 =
                                                            Obj.magic uu___8 in
                                                          Obj.magic (ret t2))
                                                         uu___8))) uu___4)))
                               uu___2))) uu___1)) in
        FStarC_Tactics_Monad.wrap_err "norm_term" uu___
let (refine_intro : unit -> unit FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
        (Obj.magic FStarC_Tactics_Monad.cur_goal)
        (fun uu___2 ->
           (fun g ->
              let g = Obj.magic g in
              let uu___2 =
                let uu___3 = FStarC_Tactics_Types.goal_env g in
                let uu___4 = FStarC_Tactics_Types.goal_type g in
                FStarC_TypeChecker_Rel.base_and_refinement uu___3 uu___4 in
              match uu___2 with
              | (uu___3, FStar_Pervasives_Native.None) ->
                  Obj.magic (FStarC_Tactics_Monad.fail "not a refinement")
              | (t, FStar_Pervasives_Native.Some (bv, phi)) ->
                  (mark_goal_implicit_already_checked g;
                   (let g1 = goal_with_type g t in
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = FStarC_Syntax_Syntax.mk_binder bv in
                          [uu___7] in
                        FStarC_Syntax_Subst.open_term uu___6 phi in
                      match uu___5 with
                      | (bvs, phi1) ->
                          let uu___6 =
                            let uu___7 = FStarC_Compiler_List.hd bvs in
                            uu___7.FStarC_Syntax_Syntax.binder_bv in
                          (uu___6, phi1) in
                    match uu___4 with
                    | (bv1, phi1) ->
                        let uu___5 =
                          let uu___6 = FStarC_Tactics_Types.goal_env g in
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    FStarC_Tactics_Types.goal_witness g in
                                  (bv1, uu___11) in
                                FStarC_Syntax_Syntax.NT uu___10 in
                              [uu___9] in
                            FStarC_Syntax_Subst.subst uu___8 phi1 in
                          let uu___8 =
                            let uu___9 = should_check_goal_uvar g in
                            FStar_Pervasives_Native.Some uu___9 in
                          FStarC_Tactics_Monad.mk_irrelevant_goal
                            "refine_intro refinement" uu___6 uu___7 uu___8
                            (rangeof g) g.FStarC_Tactics_Types.opts
                            g.FStarC_Tactics_Types.label in
                        Obj.magic
                          (FStarC_Class_Monad.op_let_Bang
                             FStarC_Tactics_Monad.monad_tac () ()
                             (Obj.magic uu___5)
                             (fun uu___6 ->
                                (fun g2 ->
                                   let g2 = Obj.magic g2 in
                                   Obj.magic
                                     (FStarC_Class_Monad.op_let_Bang
                                        FStarC_Tactics_Monad.monad_tac () ()
                                        FStarC_Tactics_Monad.dismiss
                                        (fun uu___6 ->
                                           (fun uu___6 ->
                                              let uu___6 = Obj.magic uu___6 in
                                              Obj.magic
                                                (FStarC_Tactics_Monad.add_goals
                                                   [g1; g2])) uu___6)))
                                  uu___6))))) uu___2) in
    FStarC_Tactics_Monad.wrap_err "refine_intro" uu___1
let (__exact_now :
  Prims.bool -> FStarC_Syntax_Syntax.term -> unit FStarC_Tactics_Monad.tac) =
  fun set_expected_typ ->
    fun t ->
      FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
        (Obj.magic FStarC_Tactics_Monad.cur_goal)
        (fun uu___ ->
           (fun goal ->
              let goal = Obj.magic goal in
              let env1 =
                if set_expected_typ
                then
                  let uu___ = FStarC_Tactics_Types.goal_env goal in
                  let uu___1 = FStarC_Tactics_Types.goal_type goal in
                  FStarC_TypeChecker_Env.set_expected_typ uu___ uu___1
                else FStarC_Tactics_Types.goal_env goal in
              let uu___ = __tc env1 t in
              Obj.magic
                (FStarC_Class_Monad.op_let_Bang
                   FStarC_Tactics_Monad.monad_tac () () (Obj.magic uu___)
                   (fun uu___1 ->
                      (fun uu___1 ->
                         let uu___1 = Obj.magic uu___1 in
                         match uu___1 with
                         | (t1, typ, guard) ->
                             let uu___2 =
                               FStarC_Tactics_Monad.if_verbose
                                 (fun uu___3 ->
                                    let uu___4 =
                                      FStarC_Class_Show.show
                                        FStarC_Syntax_Print.showable_term typ in
                                    let uu___5 =
                                      let uu___6 =
                                        FStarC_Tactics_Types.goal_env goal in
                                      FStarC_TypeChecker_Rel.guard_to_string
                                        uu___6 guard in
                                    FStarC_Compiler_Util.print2
                                      "__exact_now: got type %s\n__exact_now: and guard %s\n"
                                      uu___4 uu___5) in
                             Obj.magic
                               (FStarC_Class_Monad.op_let_Bang
                                  FStarC_Tactics_Monad.monad_tac () () uu___2
                                  (fun uu___3 ->
                                     (fun uu___3 ->
                                        let uu___3 = Obj.magic uu___3 in
                                        let uu___4 =
                                          let uu___5 =
                                            FStarC_Tactics_Types.goal_env
                                              goal in
                                          let uu___6 =
                                            let uu___7 =
                                              should_check_goal_uvar goal in
                                            FStar_Pervasives_Native.Some
                                              uu___7 in
                                          proc_guard "__exact typing" uu___5
                                            guard uu___6 (rangeof goal) in
                                        Obj.magic
                                          (FStarC_Class_Monad.op_let_Bang
                                             FStarC_Tactics_Monad.monad_tac
                                             () () uu___4
                                             (fun uu___5 ->
                                                (fun uu___5 ->
                                                   let uu___5 =
                                                     Obj.magic uu___5 in
                                                   let uu___6 =
                                                     FStarC_Tactics_Monad.if_verbose
                                                       (fun uu___7 ->
                                                          let uu___8 =
                                                            FStarC_Class_Show.show
                                                              FStarC_Syntax_Print.showable_term
                                                              typ in
                                                          let uu___9 =
                                                            let uu___10 =
                                                              FStarC_Tactics_Types.goal_type
                                                                goal in
                                                            FStarC_Class_Show.show
                                                              FStarC_Syntax_Print.showable_term
                                                              uu___10 in
                                                          FStarC_Compiler_Util.print2
                                                            "__exact_now: unifying %s and %s\n"
                                                            uu___8 uu___9) in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_let_Bang
                                                        FStarC_Tactics_Monad.monad_tac
                                                        () () uu___6
                                                        (fun uu___7 ->
                                                           (fun uu___7 ->
                                                              let uu___7 =
                                                                Obj.magic
                                                                  uu___7 in
                                                              let uu___8 =
                                                                let uu___9 =
                                                                  FStarC_Tactics_Types.goal_env
                                                                    goal in
                                                                let uu___10 =
                                                                  FStarC_Tactics_Types.goal_type
                                                                    goal in
                                                                do_unify true
                                                                  uu___9 typ
                                                                  uu___10 in
                                                              Obj.magic
                                                                (FStarC_Class_Monad.op_let_Bang
                                                                   FStarC_Tactics_Monad.monad_tac
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
                                                                    (mark_goal_implicit_already_checked
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
                                                                    FStarC_Tactics_Types.goal_env
                                                                    goal in
                                                                    tts
                                                                    uu___12 in
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Tactics_Types.goal_type
                                                                    goal in
                                                                    FStarC_TypeChecker_Err.print_discrepancy
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
                                                                    FStarC_Tactics_Types.goal_env
                                                                    goal in
                                                                    tts
                                                                    uu___12
                                                                    t1 in
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    FStarC_Tactics_Types.goal_env
                                                                    goal in
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Tactics_Types.goal_witness
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
    Prims.bool -> FStarC_Syntax_Syntax.term -> unit FStarC_Tactics_Monad.tac)
  =
  fun try_refine ->
    fun set_expected_typ ->
      fun tm ->
        let uu___ =
          let uu___1 =
            FStarC_Tactics_Monad.if_verbose
              (fun uu___2 ->
                 let uu___3 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     tm in
                 FStarC_Compiler_Util.print1 "t_exact: tm = %s\n" uu___3) in
          FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
            uu___1
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___2 = Obj.magic uu___2 in
                  let uu___3 =
                    let uu___4 = __exact_now set_expected_typ tm in
                    FStarC_Tactics_Monad.catch uu___4 in
                  Obj.magic
                    (FStarC_Class_Monad.op_let_Bang
                       FStarC_Tactics_Monad.monad_tac () ()
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          (fun uu___4 ->
                             let uu___4 = Obj.magic uu___4 in
                             match uu___4 with
                             | FStar_Pervasives.Inr r -> Obj.magic (ret ())
                             | FStar_Pervasives.Inl e when
                                 Prims.op_Negation try_refine ->
                                 Obj.magic (FStarC_Tactics_Monad.traise e)
                             | FStar_Pervasives.Inl e ->
                                 let uu___5 =
                                   FStarC_Tactics_Monad.if_verbose
                                     (fun uu___6 ->
                                        FStarC_Compiler_Util.print_string
                                          "__exact_now failed, trying refine...\n") in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      FStarC_Tactics_Monad.monad_tac () ()
                                      uu___5
                                      (fun uu___6 ->
                                         (fun uu___6 ->
                                            let uu___6 = Obj.magic uu___6 in
                                            let uu___7 =
                                              let uu___8 =
                                                let uu___9 =
                                                  norm
                                                    [FStar_Pervasives.Delta] in
                                                FStarC_Class_Monad.op_let_Bang
                                                  FStarC_Tactics_Monad.monad_tac
                                                  () () uu___9
                                                  (fun uu___10 ->
                                                     (fun uu___10 ->
                                                        let uu___10 =
                                                          Obj.magic uu___10 in
                                                        let uu___11 =
                                                          refine_intro () in
                                                        Obj.magic
                                                          (FStarC_Class_Monad.op_let_Bang
                                                             FStarC_Tactics_Monad.monad_tac
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
                                              FStarC_Tactics_Monad.catch
                                                uu___8 in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_let_Bang
                                                 FStarC_Tactics_Monad.monad_tac
                                                 () () (Obj.magic uu___7)
                                                 (fun uu___8 ->
                                                    (fun uu___8 ->
                                                       let uu___8 =
                                                         Obj.magic uu___8 in
                                                       match uu___8 with
                                                       | FStar_Pervasives.Inr
                                                           r ->
                                                           let uu___9 =
                                                             FStarC_Tactics_Monad.if_verbose
                                                               (fun uu___10
                                                                  ->
                                                                  FStarC_Compiler_Util.print_string
                                                                    "__exact_now: failed after refining too\n") in
                                                           Obj.magic
                                                             (FStarC_Class_Monad.op_let_Bang
                                                                FStarC_Tactics_Monad.monad_tac
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
                                                                    (ret ()))
                                                                    uu___10))
                                                       | FStar_Pervasives.Inl
                                                           uu___9 ->
                                                           let uu___10 =
                                                             FStarC_Tactics_Monad.if_verbose
                                                               (fun uu___11
                                                                  ->
                                                                  FStarC_Compiler_Util.print_string
                                                                    "__exact_now: was not a refinement\n") in
                                                           Obj.magic
                                                             (FStarC_Class_Monad.op_let_Bang
                                                                FStarC_Tactics_Monad.monad_tac
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
                                                                    (FStarC_Tactics_Monad.traise
                                                                    e))
                                                                    uu___11)))
                                                      uu___8))) uu___6)))
                            uu___4))) uu___2) in
        FStarC_Tactics_Monad.wrap_err "exact" uu___
let (try_unify_by_application :
  FStarC_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option ->
    Prims.bool ->
      env ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Syntax_Syntax.term ->
            FStarC_Compiler_Range_Type.range ->
              (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.aqual *
                FStarC_Syntax_Syntax.ctx_uvar) Prims.list
                FStarC_Tactics_Monad.tac)
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
                         (FStarC_Class_Monad.op_let_Bang
                            FStarC_Tactics_Monad.monad_tac () ()
                            (Obj.magic uu___)
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  let uu___1 = Obj.magic uu___1 in
                                  if uu___1
                                  then Obj.magic (Obj.repr (ret acc))
                                  else
                                    Obj.magic
                                      (Obj.repr
                                         (let uu___2 =
                                            FStarC_Syntax_Util.arrow_one ty11 in
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
                                                     FStarC_Syntax_Util.is_total_comp
                                                       c in
                                                   Prims.op_Negation uu___4 in
                                                 if uu___3
                                                 then
                                                   Obj.repr
                                                     (FStarC_Tactics_Monad.fail
                                                        "Codomain is effectful")
                                                 else
                                                   Obj.repr
                                                     (let uu___5 =
                                                        FStarC_Tactics_Monad.new_uvar
                                                          "apply arg" e
                                                          (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                                          should_check
                                                          typedness_deps rng in
                                                      FStarC_Class_Monad.op_let_Bang
                                                        FStarC_Tactics_Monad.monad_tac
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
                                                                    FStarC_Tactics_Monad.if_verbose
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_ctxu
                                                                    uv in
                                                                    FStarC_Compiler_Util.print1
                                                                    "t_apply: generated uvar %s\n"
                                                                    uu___9) in
                                                                  Obj.magic
                                                                    (
                                                                    FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    FStarC_Syntax_Util.comp_result
                                                                    c in
                                                                    let typ'
                                                                    =
                                                                    FStarC_Syntax_Subst.subst
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    ((b.FStarC_Syntax_Syntax.binder_bv),
                                                                    uvt)] typ in
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Syntax_Util.aqual_of_binder
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
  FStarC_TypeChecker_Env.env ->
    FStarC_Tactics_Types.goal FStar_Pervasives_Native.option ->
      (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.ctx_uvar) Prims.list
        ->
        FStarC_Tactics_Types.goal Prims.list Prims.list
          FStarC_Tactics_Monad.tac)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun env1 ->
           fun gl ->
             fun imps ->
               let one_implicit_as_goal uu___ =
                 match uu___ with
                 | (term, ctx_uvar) ->
                     let uu___1 = FStarC_Syntax_Util.head_and_args term in
                     (match uu___1 with
                      | (hd, uu___2) ->
                          let uu___3 =
                            let uu___4 = FStarC_Syntax_Subst.compress hd in
                            uu___4.FStarC_Syntax_Syntax.n in
                          (match uu___3 with
                           | FStarC_Syntax_Syntax.Tm_uvar (ctx_uvar1, uu___4)
                               ->
                               let gl1 =
                                 match gl with
                                 | FStar_Pervasives_Native.None ->
                                     let uu___5 = FStarC_Options.peek () in
                                     FStarC_Tactics_Types.mk_goal env1
                                       ctx_uvar1 uu___5 true
                                       "goal for unsolved implicit"
                                 | FStar_Pervasives_Native.Some gl2 ->
                                     {
                                       FStarC_Tactics_Types.goal_main_env =
                                         (gl2.FStarC_Tactics_Types.goal_main_env);
                                       FStarC_Tactics_Types.goal_ctx_uvar =
                                         ctx_uvar1;
                                       FStarC_Tactics_Types.opts =
                                         (gl2.FStarC_Tactics_Types.opts);
                                       FStarC_Tactics_Types.is_guard =
                                         (gl2.FStarC_Tactics_Types.is_guard);
                                       FStarC_Tactics_Types.label =
                                         (gl2.FStarC_Tactics_Types.label)
                                     } in
                               let gl2 = bnorm_goal gl1 in ret [gl2]
                           | uu___4 -> ret [])) in
               Obj.magic
                 (FStarC_Class_Monad.mapM FStarC_Tactics_Monad.monad_tac ()
                    () (fun uu___ -> (Obj.magic one_implicit_as_goal) uu___)
                    (Obj.magic imps))) uu___2 uu___1 uu___
let (t_apply :
  Prims.bool ->
    Prims.bool ->
      Prims.bool ->
        FStarC_Syntax_Syntax.term -> unit FStarC_Tactics_Monad.tac)
  =
  fun uopt ->
    fun only_match ->
      fun tc_resolved_uvars ->
        fun tm ->
          let uu___ =
            let tc_resolved_uvars1 = true in
            let uu___1 =
              FStarC_Tactics_Monad.if_verbose
                (fun uu___2 ->
                   let uu___3 =
                     FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                       uopt in
                   let uu___4 =
                     FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                       only_match in
                   let uu___5 =
                     FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                       tc_resolved_uvars1 in
                   let uu___6 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                       tm in
                   FStarC_Compiler_Util.print4
                     "t_apply: uopt %s, only_match %s, tc_resolved_uvars %s, tm = %s\n"
                     uu___3 uu___4 uu___5 uu___6) in
            FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac ()
              () uu___1
              (fun uu___2 ->
                 (fun uu___2 ->
                    let uu___2 = Obj.magic uu___2 in
                    Obj.magic
                      (FStarC_Class_Monad.op_let_Bang
                         FStarC_Tactics_Monad.monad_tac () ()
                         (Obj.magic FStarC_Tactics_Monad.get)
                         (fun uu___3 ->
                            (fun ps ->
                               let ps = Obj.magic ps in
                               Obj.magic
                                 (FStarC_Class_Monad.op_let_Bang
                                    FStarC_Tactics_Monad.monad_tac () ()
                                    (Obj.magic FStarC_Tactics_Monad.cur_goal)
                                    (fun uu___3 ->
                                       (fun goal ->
                                          let goal = Obj.magic goal in
                                          let e =
                                            FStarC_Tactics_Types.goal_env
                                              goal in
                                          let should_check =
                                            should_check_goal_uvar goal in
                                          FStarC_Tactics_Monad.register_goal
                                            goal;
                                          (let uu___4 = __tc e tm in
                                           Obj.magic
                                             (FStarC_Class_Monad.op_let_Bang
                                                FStarC_Tactics_Monad.monad_tac
                                                () () (Obj.magic uu___4)
                                                (fun uu___5 ->
                                                   (fun uu___5 ->
                                                      let uu___5 =
                                                        Obj.magic uu___5 in
                                                      match uu___5 with
                                                      | (tm1, typ, guard) ->
                                                          let uu___6 =
                                                            FStarC_Tactics_Monad.if_verbose
                                                              (fun uu___7 ->
                                                                 let uu___8 =
                                                                   FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    tm1 in
                                                                 let uu___9 =
                                                                   FStarC_Tactics_Printing.goal_to_string_verbose
                                                                    goal in
                                                                 let uu___10
                                                                   =
                                                                   FStarC_Class_Show.show
                                                                    (FStarC_Class_Show.show_list
                                                                    FStarC_Syntax_Print.showable_binding)
                                                                    e.FStarC_TypeChecker_Env.gamma in
                                                                 let uu___11
                                                                   =
                                                                   FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    typ in
                                                                 let uu___12
                                                                   =
                                                                   FStarC_TypeChecker_Rel.guard_to_string
                                                                    e guard in
                                                                 FStarC_Compiler_Util.print5
                                                                   "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\ntyp=%s\nguard=%s\n"
                                                                   uu___8
                                                                   uu___9
                                                                   uu___10
                                                                   uu___11
                                                                   uu___12) in
                                                          Obj.magic
                                                            (FStarC_Class_Monad.op_let_Bang
                                                               FStarC_Tactics_Monad.monad_tac
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
                                                                    FStarC_Tactics_Types.goal_type
                                                                    goal in
                                                                    try_unify_by_application
                                                                    (FStar_Pervasives_Native.Some
                                                                    should_check)
                                                                    only_match
                                                                    e typ1
                                                                    uu___9
                                                                    (rangeof
                                                                    goal) in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun uvs
                                                                    ->
                                                                    let uvs =
                                                                    Obj.magic
                                                                    uvs in
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_Monad.if_verbose
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    (FStarC_Common.string_of_list
                                                                    ())
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (t,
                                                                    uu___13,
                                                                    uu___14)
                                                                    ->
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    t) uvs in
                                                                    FStarC_Compiler_Util.print1
                                                                    "t_apply: found args = %s\n"
                                                                    uu___11) in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    let w =
                                                                    FStarC_Compiler_List.fold_right
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    fun w1 ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (uvt, q,
                                                                    uu___12)
                                                                    ->
                                                                    FStarC_Syntax_Util.mk_app
                                                                    w1
                                                                    [
                                                                    (uvt, q)])
                                                                    uvs tm1 in
                                                                    let uvset
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStarC_Class_Setlike.empty
                                                                    ()
                                                                    (Obj.magic
                                                                    (FStarC_Compiler_FlatSet.setlike_flat_set
                                                                    FStarC_Syntax_Free.ord_ctx_uvar))
                                                                    ()) in
                                                                    FStarC_Compiler_List.fold_right
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    fun s ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (uu___13,
                                                                    uu___14,
                                                                    uv) ->
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStarC_Syntax_Util.ctx_uvar_typ
                                                                    uv in
                                                                    FStarC_Syntax_Free.uvars
                                                                    uu___16 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Setlike.union
                                                                    ()
                                                                    (Obj.magic
                                                                    (FStarC_Compiler_FlatSet.setlike_flat_set
                                                                    FStarC_Syntax_Free.ord_ctx_uvar))
                                                                    (Obj.magic
                                                                    s)
                                                                    (Obj.magic
                                                                    uu___15)))
                                                                    uu___13
                                                                    uu___12)
                                                                    uvs
                                                                    uu___11 in
                                                                    let free_in_some_goal
                                                                    uv =
                                                                    FStarC_Class_Setlike.mem
                                                                    ()
                                                                    (Obj.magic
                                                                    (FStarC_Compiler_FlatSet.setlike_flat_set
                                                                    FStarC_Syntax_Free.ord_ctx_uvar))
                                                                    uv
                                                                    (Obj.magic
                                                                    uvset) in
                                                                    let uu___11
                                                                    =
                                                                    solve'
                                                                    goal w in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    let uvt_uv_l
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    (uvt, _q,
                                                                    uv) ->
                                                                    (uvt, uv))
                                                                    uvs in
                                                                    let uu___13
                                                                    =
                                                                    apply_implicits_as_goals
                                                                    e
                                                                    (FStar_Pervasives_Native.Some
                                                                    goal)
                                                                    uvt_uv_l in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
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
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Compiler_List.filter
                                                                    (fun g ->
                                                                    let uu___16
                                                                    =
                                                                    uopt &&
                                                                    (free_in_some_goal
                                                                    g.FStarC_Tactics_Types.goal_ctx_uvar) in
                                                                    Prims.op_Negation
                                                                    uu___16)
                                                                    (FStarC_Compiler_List.flatten
                                                                    sub_goals) in
                                                                    FStarC_Compiler_List.map
                                                                    bnorm_goal
                                                                    uu___15 in
                                                                    FStarC_Compiler_List.rev
                                                                    uu___14 in
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Tactics_Monad.add_goals
                                                                    sub_goals1 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    (proc_guard
                                                                    "apply guard"
                                                                    e guard
                                                                    (FStar_Pervasives_Native.Some
                                                                    should_check)
                                                                    (rangeof
                                                                    goal)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___7)))
                                                     uu___5)))) uu___3)))
                              uu___3))) uu___2) in
          FStarC_Tactics_Monad.wrap_err "apply" uu___
let (lemma_or_sq :
  FStarC_Syntax_Syntax.comp ->
    (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c ->
    let uu___ = FStarC_Syntax_Util.comp_eff_name_res_and_args c in
    match uu___ with
    | (eff_name, res, args) ->
        let uu___1 =
          FStarC_Ident.lid_equals eff_name
            FStarC_Parser_Const.effect_Lemma_lid in
        if uu___1
        then
          let uu___2 =
            match args with
            | pre::post::uu___3 ->
                ((FStar_Pervasives_Native.fst pre),
                  (FStar_Pervasives_Native.fst post))
            | uu___3 -> failwith "apply_lemma: impossible: not a lemma" in
          (match uu___2 with
           | (pre, post) ->
               let post1 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_Syntax_Syntax.as_arg FStarC_Syntax_Util.exp_unit in
                   [uu___4] in
                 FStarC_Syntax_Util.mk_app post uu___3 in
               FStar_Pervasives_Native.Some (pre, post1))
        else
          (let uu___3 =
             (FStarC_Syntax_Util.is_pure_effect eff_name) ||
               (FStarC_Syntax_Util.is_ghost_effect eff_name) in
           if uu___3
           then
             let uu___4 = FStarC_Syntax_Util.un_squash res in
             FStarC_Compiler_Util.map_opt uu___4
               (fun post -> (FStarC_Syntax_Util.t_true, post))
           else FStar_Pervasives_Native.None)
let rec fold_left :
  'a 'b .
    ('a -> 'b -> 'b FStarC_Tactics_Monad.tac) ->
      'b -> 'a Prims.list -> 'b FStarC_Tactics_Monad.tac
  =
  fun f ->
    fun e ->
      fun xs ->
        match xs with
        | [] -> ret e
        | x::xs1 ->
            let uu___ = f x e in
            let uu___1 = bind () in
            uu___1 uu___ (fun e' -> fold_left f e' xs1)
let (t_apply_lemma :
  Prims.bool ->
    Prims.bool -> FStarC_Syntax_Syntax.term -> unit FStarC_Tactics_Monad.tac)
  =
  fun noinst ->
    fun noinst_lhs ->
      fun tm ->
        let uu___ =
          let uu___1 =
            FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac ()
              () (Obj.magic FStarC_Tactics_Monad.get)
              (fun uu___2 ->
                 (fun ps ->
                    let ps = Obj.magic ps in
                    let uu___2 =
                      FStarC_Tactics_Monad.if_verbose
                        (fun uu___3 ->
                           let uu___4 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_term tm in
                           FStarC_Compiler_Util.print1
                             "apply_lemma: tm = %s\n" uu___4) in
                    Obj.magic
                      (FStarC_Class_Monad.op_let_Bang
                         FStarC_Tactics_Monad.monad_tac () () uu___2
                         (fun uu___3 ->
                            (fun uu___3 ->
                               let uu___3 = Obj.magic uu___3 in
                               let is_unit_t t =
                                 let uu___4 =
                                   let uu___5 =
                                     FStarC_Syntax_Subst.compress t in
                                   uu___5.FStarC_Syntax_Syntax.n in
                                 match uu___4 with
                                 | FStarC_Syntax_Syntax.Tm_fvar fv when
                                     FStarC_Syntax_Syntax.fv_eq_lid fv
                                       FStarC_Parser_Const.unit_lid
                                     -> true
                                 | uu___5 -> false in
                               Obj.magic
                                 (FStarC_Class_Monad.op_let_Bang
                                    FStarC_Tactics_Monad.monad_tac () ()
                                    (Obj.magic FStarC_Tactics_Monad.cur_goal)
                                    (fun uu___4 ->
                                       (fun goal ->
                                          let goal = Obj.magic goal in
                                          let env1 =
                                            FStarC_Tactics_Types.goal_env
                                              goal in
                                          FStarC_Tactics_Monad.register_goal
                                            goal;
                                          (let uu___5 = __tc env1 tm in
                                           Obj.magic
                                             (FStarC_Class_Monad.op_let_Bang
                                                FStarC_Tactics_Monad.monad_tac
                                                () () (Obj.magic uu___5)
                                                (fun uu___6 ->
                                                   (fun uu___6 ->
                                                      let uu___6 =
                                                        Obj.magic uu___6 in
                                                      match uu___6 with
                                                      | (tm1, t, guard) ->
                                                          let uu___7 =
                                                            FStarC_Syntax_Util.arrow_formals_comp
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
                                                                    (FStarC_Tactics_Monad.fail
                                                                    "not a lemma or squashed function")
                                                                | FStar_Pervasives_Native.Some
                                                                    (pre,
                                                                    post) ->
                                                                    let uu___9
                                                                    =
                                                                    fold_left
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    fun
                                                                    uu___11
                                                                    ->
                                                                    match 
                                                                    (uu___10,
                                                                    uu___11)
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = b;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = aq;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___12;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___13;_},
                                                                    (uvs,
                                                                    deps,
                                                                    imps,
                                                                    subst))
                                                                    ->
                                                                    let b_t =
                                                                    FStarC_Syntax_Subst.subst
                                                                    subst
                                                                    b.FStarC_Syntax_Syntax.sort in
                                                                    let uu___14
                                                                    =
                                                                    is_unit_t
                                                                    b_t in
                                                                    if
                                                                    uu___14
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (ret
                                                                    (((FStarC_Syntax_Util.exp_unit,
                                                                    aq) ::
                                                                    uvs),
                                                                    deps,
                                                                    imps,
                                                                    ((FStarC_Syntax_Syntax.NT
                                                                    (b,
                                                                    FStarC_Syntax_Util.exp_unit))
                                                                    ::
                                                                    subst))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
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
                                                                    FStarC_Syntax_Syntax.Strict
                                                                    ->
                                                                    FStarC_Syntax_Syntax.Allow_ghost
                                                                    "apply lemma uvar"
                                                                    | 
                                                                    x -> x in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___18 in
                                                                    FStarC_Tactics_Monad.new_uvar
                                                                    "apply_lemma"
                                                                    env1 b_t
                                                                    uu___17
                                                                    deps
                                                                    (rangeof
                                                                    goal) in
                                                                    FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    (FStarC_Compiler_Debug.medium
                                                                    ()) ||
                                                                    (FStarC_Compiler_Effect.op_Bang
                                                                    dbg_2635) in
                                                                    if
                                                                    uu___19
                                                                    then
                                                                    let uu___20
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_ctxu
                                                                    u in
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    tm1 in
                                                                    FStarC_Compiler_Util.print2
                                                                    "Apply lemma created a new uvar %s while applying %s\n"
                                                                    uu___20
                                                                    uu___21
                                                                    else ());
                                                                    Obj.magic
                                                                    (ret
                                                                    (((t1,
                                                                    aq) ::
                                                                    uvs), (u
                                                                    :: deps),
                                                                    ((t1, u)
                                                                    :: imps),
                                                                    ((FStarC_Syntax_Syntax.NT
                                                                    (b, t1))
                                                                    ::
                                                                    subst)))))
                                                                    uu___17))))
                                                                    uu___11
                                                                    uu___10)
                                                                    ([], [],
                                                                    [], [])
                                                                    bs in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    FStarC_Compiler_List.rev
                                                                    implicits1 in
                                                                    let uvs1
                                                                    =
                                                                    FStarC_Compiler_List.rev
                                                                    uvs in
                                                                    let pre1
                                                                    =
                                                                    FStarC_Syntax_Subst.subst
                                                                    subst pre in
                                                                    let post1
                                                                    =
                                                                    FStarC_Syntax_Subst.subst
                                                                    subst
                                                                    post in
                                                                    let post_u
                                                                    =
                                                                    env1.FStarC_TypeChecker_Env.universe_of
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
                                                                    FStarC_Tactics_Types.goal_type
                                                                    goal in
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Syntax_Util.mk_squash
                                                                    post_u
                                                                    post1 in
                                                                    cmp_func
                                                                    must_tot
                                                                    env1
                                                                    uu___13
                                                                    uu___14 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    FStarC_Syntax_Util.mk_squash
                                                                    post_u
                                                                    post1 in
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Tactics_Types.goal_type
                                                                    goal in
                                                                    FStarC_TypeChecker_Err.print_discrepancy
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
                                                                    FStarC_Syntax_Util.exp_unit in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    let free_uvars
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStarC_Syntax_Free.uvars
                                                                    t1 in
                                                                    FStarC_Class_Setlike.elems
                                                                    ()
                                                                    (Obj.magic
                                                                    (FStarC_Compiler_FlatSet.setlike_flat_set
                                                                    FStarC_Syntax_Free.ord_ctx_uvar))
                                                                    (Obj.magic
                                                                    uu___17) in
                                                                    FStarC_Compiler_List.map
                                                                    (fun x ->
                                                                    x.FStarC_Syntax_Syntax.ctx_uvar_head)
                                                                    uu___16 in
                                                                    FStarC_Compiler_List.existsML
                                                                    (fun u ->
                                                                    FStarC_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars in
                                                                    let appears
                                                                    uv goals
                                                                    =
                                                                    FStarC_Compiler_List.existsML
                                                                    (fun g'
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    FStarC_Tactics_Types.goal_type
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
                                                                    FStarC_Syntax_Util.head_and_args
                                                                    t1 in
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu___17)
                                                                    ->
                                                                    (match 
                                                                    hd.FStarC_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_uvar
                                                                    (uv,
                                                                    uu___18)
                                                                    ->
                                                                    appears
                                                                    uv.FStarC_Syntax_Syntax.ctx_uvar_head
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
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    FStarC_Compiler_List.flatten
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
                                                                    FStarC_Tactics_Types.goal_witness
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
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    env1.FStarC_TypeChecker_Env.universe_of
                                                                    env1 pre1 in
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStarC_TypeChecker_Common.NonTrivial
                                                                    pre1) in
                                                                    FStarC_TypeChecker_Rel.simplify_guard
                                                                    env1
                                                                    uu___22 in
                                                                    uu___21.FStarC_TypeChecker_Common.guard_f in
                                                                    match uu___20
                                                                    with
                                                                    | 
                                                                    FStarC_TypeChecker_Common.Trivial
                                                                    -> 
                                                                    ret ()
                                                                    | 
                                                                    FStarC_TypeChecker_Common.NonTrivial
                                                                    uu___21
                                                                    ->
                                                                    FStarC_Tactics_Monad.add_irrelevant_goal
                                                                    goal
                                                                    "apply_lemma precondition"
                                                                    env1 pre1
                                                                    (FStar_Pervasives_Native.Some
                                                                    goal_sc) in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    (FStarC_Tactics_Monad.add_goals
                                                                    sub_goals2))
                                                                    uu___20)))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    uu___15))))
                                                                    uu___13)))
                                                                    uu___10)))))
                                                     uu___6)))) uu___4)))
                              uu___3))) uu___2) in
          focus uu___1 in
        FStarC_Tactics_Monad.wrap_err "apply_lemma" uu___
let (split_env :
  FStarC_Syntax_Syntax.bv ->
    env ->
      (env * FStarC_Syntax_Syntax.bv * FStarC_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar ->
    fun e ->
      let rec aux e1 =
        let uu___ = FStarC_TypeChecker_Env.pop_bv e1 in
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv', e') ->
            let uu___1 = FStarC_Syntax_Syntax.bv_eq bvar bv' in
            if uu___1
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu___3 = aux e' in
               FStarC_Compiler_Util.map_opt uu___3
                 (fun uu___4 ->
                    match uu___4 with
                    | (e'', bv, bvs) -> (e'', bv, (bv' :: bvs)))) in
      let uu___ = aux e in
      FStarC_Compiler_Util.map_opt uu___
        (fun uu___1 ->
           match uu___1 with
           | (e', bv, bvs) -> (e', bv, (FStarC_Compiler_List.rev bvs)))
let (subst_goal :
  FStarC_Syntax_Syntax.bv ->
    FStarC_Syntax_Syntax.bv ->
      FStarC_Tactics_Types.goal ->
        (FStarC_Syntax_Syntax.bv * FStarC_Tactics_Types.goal)
          FStar_Pervasives_Native.option FStarC_Tactics_Monad.tac)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun b1 ->
           fun b2 ->
             fun g ->
               let uu___ =
                 let uu___1 = FStarC_Tactics_Types.goal_env g in
                 split_env b1 uu___1 in
               match uu___ with
               | FStar_Pervasives_Native.Some (e0, b11, bvs) ->
                   Obj.magic
                     (Obj.repr
                        (let bs =
                           FStarC_Compiler_List.map
                             FStarC_Syntax_Syntax.mk_binder (b11 :: bvs) in
                         let t = FStarC_Tactics_Types.goal_type g in
                         let uu___1 =
                           let uu___2 = FStarC_Syntax_Subst.close_binders bs in
                           let uu___3 = FStarC_Syntax_Subst.close bs t in
                           (uu___2, uu___3) in
                         match uu___1 with
                         | (bs', t') ->
                             let bs'1 =
                               let uu___2 = FStarC_Syntax_Syntax.mk_binder b2 in
                               let uu___3 = FStarC_Compiler_List.tail bs' in
                               uu___2 :: uu___3 in
                             let uu___2 =
                               FStarC_TypeChecker_Core.open_binders_in_term
                                 e0 bs'1 t' in
                             (match uu___2 with
                              | (new_env, bs'', t'') ->
                                  let b21 =
                                    let uu___3 = FStarC_Compiler_List.hd bs'' in
                                    uu___3.FStarC_Syntax_Syntax.binder_bv in
                                  let uu___3 =
                                    let uu___4 =
                                      let uu___5 = should_check_goal_uvar g in
                                      FStar_Pervasives_Native.Some uu___5 in
                                    let uu___5 = goal_typedness_deps g in
                                    FStarC_Tactics_Monad.new_uvar
                                      "subst_goal" new_env t'' uu___4 uu___5
                                      (rangeof g) in
                                  FStarC_Class_Monad.op_let_Bang
                                    FStarC_Tactics_Monad.monad_tac () ()
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun uu___4 ->
                                          let uu___4 = Obj.magic uu___4 in
                                          match uu___4 with
                                          | (uvt, uv) ->
                                              let goal' =
                                                FStarC_Tactics_Types.mk_goal
                                                  new_env uv
                                                  g.FStarC_Tactics_Types.opts
                                                  g.FStarC_Tactics_Types.is_guard
                                                  g.FStarC_Tactics_Types.label in
                                              let sol =
                                                let uu___5 =
                                                  FStarC_Syntax_Util.abs bs''
                                                    uvt
                                                    FStar_Pervasives_Native.None in
                                                let uu___6 =
                                                  FStarC_Compiler_List.map
                                                    (fun uu___7 ->
                                                       match uu___7 with
                                                       | {
                                                           FStarC_Syntax_Syntax.binder_bv
                                                             = bv;
                                                           FStarC_Syntax_Syntax.binder_qual
                                                             = q;
                                                           FStarC_Syntax_Syntax.binder_positivity
                                                             = uu___8;
                                                           FStarC_Syntax_Syntax.binder_attrs
                                                             = uu___9;_}
                                                           ->
                                                           let uu___10 =
                                                             FStarC_Syntax_Syntax.bv_to_name
                                                               bv in
                                                           FStarC_Syntax_Syntax.as_arg
                                                             uu___10) bs in
                                                FStarC_Syntax_Util.mk_app
                                                  uu___5 uu___6 in
                                              let uu___5 = set_solution g sol in
                                              Obj.magic
                                                (FStarC_Class_Monad.op_let_Bang
                                                   FStarC_Tactics_Monad.monad_tac
                                                   () () uu___5
                                                   (fun uu___6 ->
                                                      (fun uu___6 ->
                                                         let uu___6 =
                                                           Obj.magic uu___6 in
                                                         Obj.magic
                                                           (ret
                                                              (FStar_Pervasives_Native.Some
                                                                 (b21, goal'))))
                                                        uu___6))) uu___4))))
               | FStar_Pervasives_Native.None ->
                   Obj.magic (Obj.repr (ret FStar_Pervasives_Native.None)))
          uu___2 uu___1 uu___
let (rewrite : FStarC_Syntax_Syntax.binder -> unit FStarC_Tactics_Monad.tac)
  =
  fun h ->
    let uu___ =
      FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
        (Obj.magic FStarC_Tactics_Monad.cur_goal)
        (fun uu___1 ->
           (fun goal ->
              let goal = Obj.magic goal in
              let bv = h.FStarC_Syntax_Syntax.binder_bv in
              let uu___1 =
                FStarC_Tactics_Monad.if_verbose
                  (fun uu___2 ->
                     let uu___3 =
                       FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv
                         bv in
                     let uu___4 =
                       FStarC_Class_Show.show
                         FStarC_Syntax_Print.showable_term
                         bv.FStarC_Syntax_Syntax.sort in
                     FStarC_Compiler_Util.print2 "+++Rewrite %s : %s\n"
                       uu___3 uu___4) in
              Obj.magic
                (FStarC_Class_Monad.op_let_Bang
                   FStarC_Tactics_Monad.monad_tac () () uu___1
                   (fun uu___2 ->
                      (fun uu___2 ->
                         let uu___2 = Obj.magic uu___2 in
                         let uu___3 =
                           let uu___4 = FStarC_Tactics_Types.goal_env goal in
                           split_env bv uu___4 in
                         match uu___3 with
                         | FStar_Pervasives_Native.None ->
                             Obj.magic
                               (FStarC_Tactics_Monad.fail
                                  "binder not found in environment")
                         | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                             let uu___4 =
                               destruct_eq e0 bv1.FStarC_Syntax_Syntax.sort in
                             (match uu___4 with
                              | FStar_Pervasives_Native.Some (x, e) ->
                                  let uu___5 =
                                    let uu___6 =
                                      FStarC_Syntax_Subst.compress x in
                                    uu___6.FStarC_Syntax_Syntax.n in
                                  (match uu___5 with
                                   | FStarC_Syntax_Syntax.Tm_name x1 ->
                                       let s =
                                         [FStarC_Syntax_Syntax.NT (x1, e)] in
                                       let t =
                                         FStarC_Tactics_Types.goal_type goal in
                                       let bs =
                                         FStarC_Compiler_List.map
                                           FStarC_Syntax_Syntax.mk_binder bvs in
                                       let uu___6 =
                                         let uu___7 =
                                           FStarC_Syntax_Subst.close_binders
                                             bs in
                                         let uu___8 =
                                           FStarC_Syntax_Subst.close bs t in
                                         (uu___7, uu___8) in
                                       (match uu___6 with
                                        | (bs', t') ->
                                            let uu___7 =
                                              let uu___8 =
                                                FStarC_Syntax_Subst.subst_binders
                                                  s bs' in
                                              let uu___9 =
                                                FStarC_Syntax_Subst.subst s
                                                  t' in
                                              (uu___8, uu___9) in
                                            (match uu___7 with
                                             | (bs'1, t'1) ->
                                                 let e01 =
                                                   FStarC_TypeChecker_Env.push_bvs
                                                     e0 [bv1] in
                                                 let uu___8 =
                                                   FStarC_TypeChecker_Core.open_binders_in_term
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
                                                          goal_typedness_deps
                                                            goal in
                                                        FStarC_Tactics_Monad.new_uvar
                                                          "rewrite" new_env
                                                          t'' uu___10 uu___11
                                                          (rangeof goal) in
                                                      Obj.magic
                                                        (FStarC_Class_Monad.op_let_Bang
                                                           FStarC_Tactics_Monad.monad_tac
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
                                                                    FStarC_Tactics_Types.mk_goal
                                                                    new_env
                                                                    uv
                                                                    goal.FStarC_Tactics_Types.opts
                                                                    goal.FStarC_Tactics_Types.is_guard
                                                                    goal.FStarC_Tactics_Types.label in
                                                                    let sol =
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Syntax_Util.abs
                                                                    bs'' uvt
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = bv2;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___14;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___15;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___16;_}
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    bv2 in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___17)
                                                                    bs in
                                                                    FStarC_Syntax_Util.mk_app
                                                                    uu___11
                                                                    uu___12 in
                                                                    let uu___11
                                                                    =
                                                                    set_solution
                                                                    goal sol in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    (FStarC_Tactics_Monad.replace_cur
                                                                    goal'))
                                                                    uu___12)))
                                                                uu___10)))))
                                   | uu___6 ->
                                       Obj.magic
                                         (FStarC_Tactics_Monad.fail
                                            "Not an equality hypothesis with a variable on the LHS"))
                              | uu___5 ->
                                  Obj.magic
                                    (FStarC_Tactics_Monad.fail
                                       "Not an equality hypothesis"))) uu___2)))
             uu___1) in
    FStarC_Tactics_Monad.wrap_err "rewrite" uu___
let (rename_to :
  FStarC_Syntax_Syntax.binder ->
    Prims.string -> FStarC_Syntax_Syntax.binder FStarC_Tactics_Monad.tac)
  =
  fun b ->
    fun s ->
      let uu___ =
        Obj.magic
          (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac ()
             () (Obj.magic FStarC_Tactics_Monad.cur_goal)
             (fun uu___1 ->
                (fun goal ->
                   let goal = Obj.magic goal in
                   let bv = b.FStarC_Syntax_Syntax.binder_bv in
                   let bv' =
                     let uu___1 =
                       let uu___2 =
                         let uu___3 =
                           let uu___4 =
                             FStarC_Ident.range_of_id
                               bv.FStarC_Syntax_Syntax.ppname in
                           (s, uu___4) in
                         FStarC_Ident.mk_ident uu___3 in
                       {
                         FStarC_Syntax_Syntax.ppname = uu___2;
                         FStarC_Syntax_Syntax.index =
                           (bv.FStarC_Syntax_Syntax.index);
                         FStarC_Syntax_Syntax.sort =
                           (bv.FStarC_Syntax_Syntax.sort)
                       } in
                     FStarC_Syntax_Syntax.freshen_bv uu___1 in
                   let uu___1 = subst_goal bv bv' goal in
                   Obj.magic
                     (FStarC_Class_Monad.op_let_Bang
                        FStarC_Tactics_Monad.monad_tac () ()
                        (Obj.magic uu___1)
                        (fun uu___2 ->
                           (fun uu___2 ->
                              let uu___2 = Obj.magic uu___2 in
                              match uu___2 with
                              | FStar_Pervasives_Native.None ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStarC_Tactics_Monad.fail
                                          "binder not found in environment"))
                              | FStar_Pervasives_Native.Some (bv'1, goal1) ->
                                  Obj.magic
                                    (Obj.repr
                                       (let uu___3 =
                                          FStarC_Tactics_Monad.replace_cur
                                            goal1 in
                                        FStarC_Class_Monad.op_let_Bang
                                          FStarC_Tactics_Monad.monad_tac ()
                                          () uu___3
                                          (fun uu___4 ->
                                             (fun uu___4 ->
                                                let uu___4 = Obj.magic uu___4 in
                                                Obj.magic
                                                  (ret
                                                     {
                                                       FStarC_Syntax_Syntax.binder_bv
                                                         = bv'1;
                                                       FStarC_Syntax_Syntax.binder_qual
                                                         =
                                                         (b.FStarC_Syntax_Syntax.binder_qual);
                                                       FStarC_Syntax_Syntax.binder_positivity
                                                         =
                                                         (b.FStarC_Syntax_Syntax.binder_positivity);
                                                       FStarC_Syntax_Syntax.binder_attrs
                                                         =
                                                         (b.FStarC_Syntax_Syntax.binder_attrs)
                                                     })) uu___4)))) uu___2)))
                  uu___1)) in
      FStarC_Tactics_Monad.wrap_err "rename_to" uu___
let (binder_retype :
  FStarC_Syntax_Syntax.binder -> unit FStarC_Tactics_Monad.tac) =
  fun b ->
    let uu___ =
      FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
        (Obj.magic FStarC_Tactics_Monad.cur_goal)
        (fun uu___1 ->
           (fun goal ->
              let goal = Obj.magic goal in
              let bv = b.FStarC_Syntax_Syntax.binder_bv in
              let uu___1 =
                let uu___2 = FStarC_Tactics_Types.goal_env goal in
                split_env bv uu___2 in
              match uu___1 with
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (FStarC_Tactics_Monad.fail
                       "binder is not present in environment")
              | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                  let uu___2 = FStarC_Syntax_Util.type_u () in
                  (match uu___2 with
                   | (ty, u) ->
                       let goal_sc = should_check_goal_uvar goal in
                       let uu___3 =
                         let uu___4 = goal_typedness_deps goal in
                         FStarC_Tactics_Monad.new_uvar "binder_retype" e0 ty
                           (FStar_Pervasives_Native.Some goal_sc) uu___4
                           (rangeof goal) in
                       Obj.magic
                         (FStarC_Class_Monad.op_let_Bang
                            FStarC_Tactics_Monad.monad_tac () ()
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun uu___4 ->
                                  let uu___4 = Obj.magic uu___4 in
                                  match uu___4 with
                                  | (t', u_t') ->
                                      let bv'' =
                                        {
                                          FStarC_Syntax_Syntax.ppname =
                                            (bv1.FStarC_Syntax_Syntax.ppname);
                                          FStarC_Syntax_Syntax.index =
                                            (bv1.FStarC_Syntax_Syntax.index);
                                          FStarC_Syntax_Syntax.sort = t'
                                        } in
                                      let s =
                                        let uu___5 =
                                          let uu___6 =
                                            let uu___7 =
                                              FStarC_Syntax_Syntax.bv_to_name
                                                bv'' in
                                            (bv1, uu___7) in
                                          FStarC_Syntax_Syntax.NT uu___6 in
                                        [uu___5] in
                                      let bvs1 =
                                        FStarC_Compiler_List.map
                                          (fun b1 ->
                                             let uu___5 =
                                               FStarC_Syntax_Subst.subst s
                                                 b1.FStarC_Syntax_Syntax.sort in
                                             {
                                               FStarC_Syntax_Syntax.ppname =
                                                 (b1.FStarC_Syntax_Syntax.ppname);
                                               FStarC_Syntax_Syntax.index =
                                                 (b1.FStarC_Syntax_Syntax.index);
                                               FStarC_Syntax_Syntax.sort =
                                                 uu___5
                                             }) bvs in
                                      let env' =
                                        FStarC_TypeChecker_Env.push_bvs e0
                                          (bv'' :: bvs1) in
                                      Obj.magic
                                        (FStarC_Class_Monad.op_let_Bang
                                           FStarC_Tactics_Monad.monad_tac ()
                                           () FStarC_Tactics_Monad.dismiss
                                           (fun uu___5 ->
                                              (fun uu___5 ->
                                                 let uu___5 =
                                                   Obj.magic uu___5 in
                                                 let new_goal =
                                                   let uu___6 =
                                                     FStarC_Tactics_Types.goal_with_env
                                                       goal env' in
                                                   let uu___7 =
                                                     let uu___8 =
                                                       FStarC_Tactics_Types.goal_type
                                                         goal in
                                                     FStarC_Syntax_Subst.subst
                                                       s uu___8 in
                                                   goal_with_type uu___6
                                                     uu___7 in
                                                 let uu___6 =
                                                   FStarC_Tactics_Monad.add_goals
                                                     [new_goal] in
                                                 Obj.magic
                                                   (FStarC_Class_Monad.op_let_Bang
                                                      FStarC_Tactics_Monad.monad_tac
                                                      () () uu___6
                                                      (fun uu___7 ->
                                                         (fun uu___7 ->
                                                            let uu___7 =
                                                              Obj.magic
                                                                uu___7 in
                                                            let uu___8 =
                                                              FStarC_Syntax_Util.mk_eq2
                                                                (FStarC_Syntax_Syntax.U_succ
                                                                   u) ty
                                                                bv1.FStarC_Syntax_Syntax.sort
                                                                t' in
                                                            Obj.magic
                                                              (FStarC_Tactics_Monad.add_irrelevant_goal
                                                                 goal
                                                                 "binder_retype equation"
                                                                 e0 uu___8
                                                                 (FStar_Pervasives_Native.Some
                                                                    goal_sc)))
                                                           uu___7))) uu___5)))
                                 uu___4)))) uu___1) in
    FStarC_Tactics_Monad.wrap_err "binder_retype" uu___
let (norm_binder_type :
  FStar_Pervasives.norm_step Prims.list ->
    FStarC_Syntax_Syntax.binder -> unit FStarC_Tactics_Monad.tac)
  =
  fun s ->
    fun b ->
      let uu___ =
        FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
          (Obj.magic FStarC_Tactics_Monad.cur_goal)
          (fun uu___1 ->
             (fun goal ->
                let goal = Obj.magic goal in
                let bv = b.FStarC_Syntax_Syntax.binder_bv in
                let uu___1 =
                  let uu___2 = FStarC_Tactics_Types.goal_env goal in
                  split_env bv uu___2 in
                match uu___1 with
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (FStarC_Tactics_Monad.fail
                         "binder is not present in environment")
                | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                    let steps =
                      let uu___2 =
                        FStarC_TypeChecker_Cfg.translate_norm_steps s in
                      FStarC_Compiler_List.op_At
                        [FStarC_TypeChecker_Env.Reify;
                        FStarC_TypeChecker_Env.DontUnfoldAttr
                          [FStarC_Parser_Const.tac_opaque_attr]] uu___2 in
                    let sort' =
                      normalize steps e0 bv1.FStarC_Syntax_Syntax.sort in
                    let bv' =
                      {
                        FStarC_Syntax_Syntax.ppname =
                          (bv1.FStarC_Syntax_Syntax.ppname);
                        FStarC_Syntax_Syntax.index =
                          (bv1.FStarC_Syntax_Syntax.index);
                        FStarC_Syntax_Syntax.sort = sort'
                      } in
                    let env' =
                      FStarC_TypeChecker_Env.push_bvs e0 (bv' :: bvs) in
                    let uu___2 = FStarC_Tactics_Types.goal_with_env goal env' in
                    Obj.magic (FStarC_Tactics_Monad.replace_cur uu___2))
               uu___1) in
      FStarC_Tactics_Monad.wrap_err "norm_binder_type" uu___
let (revert : unit -> unit FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
      (Obj.magic FStarC_Tactics_Monad.cur_goal)
      (fun uu___1 ->
         (fun goal ->
            let goal = Obj.magic goal in
            let uu___1 =
              let uu___2 = FStarC_Tactics_Types.goal_env goal in
              FStarC_TypeChecker_Env.pop_bv uu___2 in
            match uu___1 with
            | FStar_Pervasives_Native.None ->
                Obj.magic
                  (FStarC_Tactics_Monad.fail "Cannot revert; empty context")
            | FStar_Pervasives_Native.Some (x, env') ->
                let typ' =
                  let uu___2 =
                    let uu___3 = FStarC_Syntax_Syntax.mk_binder x in [uu___3] in
                  let uu___3 =
                    let uu___4 = FStarC_Tactics_Types.goal_type goal in
                    FStarC_Syntax_Syntax.mk_Total uu___4 in
                  FStarC_Syntax_Util.arrow uu___2 uu___3 in
                let uu___2 =
                  let uu___3 =
                    let uu___4 = should_check_goal_uvar goal in
                    FStar_Pervasives_Native.Some uu___4 in
                  let uu___4 = goal_typedness_deps goal in
                  FStarC_Tactics_Monad.new_uvar "revert" env' typ' uu___3
                    uu___4 (rangeof goal) in
                Obj.magic
                  (FStarC_Class_Monad.op_let_Bang
                     FStarC_Tactics_Monad.monad_tac () () (Obj.magic uu___2)
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
                                         FStarC_Syntax_Syntax.bv_to_name x in
                                       FStarC_Syntax_Syntax.as_arg uu___8 in
                                     [uu___7] in
                                   let uu___7 =
                                     let uu___8 =
                                       FStarC_Tactics_Types.goal_type goal in
                                     uu___8.FStarC_Syntax_Syntax.pos in
                                   FStarC_Syntax_Syntax.mk_Tm_app r uu___6
                                     uu___7 in
                                 set_solution goal uu___5 in
                               Obj.magic
                                 (FStarC_Class_Monad.op_let_Bang
                                    FStarC_Tactics_Monad.monad_tac () ()
                                    uu___4
                                    (fun uu___5 ->
                                       (fun uu___5 ->
                                          let uu___5 = Obj.magic uu___5 in
                                          let g =
                                            FStarC_Tactics_Types.mk_goal env'
                                              u_r
                                              goal.FStarC_Tactics_Types.opts
                                              goal.FStarC_Tactics_Types.is_guard
                                              goal.FStarC_Tactics_Types.label in
                                          Obj.magic
                                            (FStarC_Tactics_Monad.replace_cur
                                               g)) uu___5))) uu___3))) uu___1)
let (free_in :
  FStarC_Syntax_Syntax.bv -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun bv ->
    fun t ->
      let uu___ = FStarC_Syntax_Free.names t in
      FStarC_Class_Setlike.mem ()
        (Obj.magic
           (FStarC_Compiler_FlatSet.setlike_flat_set
              FStarC_Syntax_Syntax.ord_bv)) bv (Obj.magic uu___)
let (clear : FStarC_Syntax_Syntax.binder -> unit FStarC_Tactics_Monad.tac) =
  fun b ->
    let bv = b.FStarC_Syntax_Syntax.binder_bv in
    FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
      (Obj.magic FStarC_Tactics_Monad.cur_goal)
      (fun uu___ ->
         (fun goal ->
            let goal = Obj.magic goal in
            let uu___ =
              FStarC_Tactics_Monad.if_verbose
                (fun uu___1 ->
                   let uu___2 =
                     FStarC_Class_Show.show
                       FStarC_Syntax_Print.showable_binder b in
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = FStarC_Tactics_Types.goal_env goal in
                         FStarC_TypeChecker_Env.all_binders uu___6 in
                       FStarC_Compiler_List.length uu___5 in
                     FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                       uu___4 in
                   FStarC_Compiler_Util.print2
                     "Clear of (%s), env has %s binders\n" uu___2 uu___3) in
            Obj.magic
              (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac
                 () () uu___
                 (fun uu___1 ->
                    (fun uu___1 ->
                       let uu___1 = Obj.magic uu___1 in
                       let uu___2 =
                         let uu___3 = FStarC_Tactics_Types.goal_env goal in
                         split_env bv uu___3 in
                       match uu___2 with
                       | FStar_Pervasives_Native.None ->
                           Obj.magic
                             (FStarC_Tactics_Monad.fail
                                "Cannot clear; binder not in environment")
                       | FStar_Pervasives_Native.Some (e', bv1, bvs) ->
                           let rec check bvs1 =
                             match bvs1 with
                             | [] -> ret ()
                             | bv'::bvs2 ->
                                 let uu___3 =
                                   free_in bv1 bv'.FStarC_Syntax_Syntax.sort in
                                 if uu___3
                                 then
                                   let uu___4 =
                                     let uu___5 =
                                       FStarC_Class_Show.show
                                         FStarC_Syntax_Print.showable_bv bv' in
                                     FStarC_Compiler_Util.format1
                                       "Cannot clear; binder present in the type of %s"
                                       uu___5 in
                                   FStarC_Tactics_Monad.fail uu___4
                                 else check bvs2 in
                           let uu___3 =
                             let uu___4 = FStarC_Tactics_Types.goal_type goal in
                             free_in bv1 uu___4 in
                           if uu___3
                           then
                             Obj.magic
                               (FStarC_Tactics_Monad.fail
                                  "Cannot clear; binder present in goal")
                           else
                             (let uu___5 = check bvs in
                              Obj.magic
                                (FStarC_Class_Monad.op_let_Bang
                                   FStarC_Tactics_Monad.monad_tac () ()
                                   uu___5
                                   (fun uu___6 ->
                                      (fun uu___6 ->
                                         let uu___6 = Obj.magic uu___6 in
                                         let env' =
                                           FStarC_TypeChecker_Env.push_bvs e'
                                             bvs in
                                         let uu___7 =
                                           let uu___8 =
                                             FStarC_Tactics_Types.goal_type
                                               goal in
                                           let uu___9 =
                                             let uu___10 =
                                               should_check_goal_uvar goal in
                                             FStar_Pervasives_Native.Some
                                               uu___10 in
                                           let uu___10 =
                                             goal_typedness_deps goal in
                                           FStarC_Tactics_Monad.new_uvar
                                             "clear.witness" env' uu___8
                                             uu___9 uu___10 (rangeof goal) in
                                         Obj.magic
                                           (FStarC_Class_Monad.op_let_Bang
                                              FStarC_Tactics_Monad.monad_tac
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
                                                          (FStarC_Class_Monad.op_let_Bang
                                                             FStarC_Tactics_Monad.monad_tac
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
                                                                    FStarC_Tactics_Types.mk_goal
                                                                    env'
                                                                    uvar_ut
                                                                    goal.FStarC_Tactics_Types.opts
                                                                    goal.FStarC_Tactics_Types.is_guard
                                                                    goal.FStarC_Tactics_Types.label in
                                                                   Obj.magic
                                                                    (FStarC_Tactics_Monad.replace_cur
                                                                    uu___11))
                                                                  uu___10)))
                                                   uu___8))) uu___6))))
                      uu___1))) uu___)
let (clear_top : unit -> unit FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
      (Obj.magic FStarC_Tactics_Monad.cur_goal)
      (fun uu___1 ->
         (fun goal ->
            let goal = Obj.magic goal in
            let uu___1 =
              let uu___2 = FStarC_Tactics_Types.goal_env goal in
              FStarC_TypeChecker_Env.pop_bv uu___2 in
            match uu___1 with
            | FStar_Pervasives_Native.None ->
                Obj.magic
                  (FStarC_Tactics_Monad.fail "Cannot clear; empty context")
            | FStar_Pervasives_Native.Some (x, uu___2) ->
                let uu___3 = FStarC_Syntax_Syntax.mk_binder x in
                Obj.magic (clear uu___3)) uu___1)
let (prune : Prims.string -> unit FStarC_Tactics_Monad.tac) =
  fun s ->
    FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
      (Obj.magic FStarC_Tactics_Monad.cur_goal)
      (fun uu___ ->
         (fun g ->
            let g = Obj.magic g in
            let ctx = FStarC_Tactics_Types.goal_env g in
            let ctx' =
              let uu___ = FStarC_Ident.path_of_text s in
              FStarC_TypeChecker_Env.rem_proof_ns ctx uu___ in
            let g' = FStarC_Tactics_Types.goal_with_env g ctx' in
            Obj.magic (FStarC_Tactics_Monad.replace_cur g')) uu___)
let (addns : Prims.string -> unit FStarC_Tactics_Monad.tac) =
  fun s ->
    FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
      (Obj.magic FStarC_Tactics_Monad.cur_goal)
      (fun uu___ ->
         (fun g ->
            let g = Obj.magic g in
            let ctx = FStarC_Tactics_Types.goal_env g in
            let ctx' =
              let uu___ = FStarC_Ident.path_of_text s in
              FStarC_TypeChecker_Env.add_proof_ns ctx uu___ in
            let g' = FStarC_Tactics_Types.goal_with_env g ctx' in
            Obj.magic (FStarC_Tactics_Monad.replace_cur g')) uu___)
let (guard_formula :
  FStarC_TypeChecker_Common.guard_t -> FStarC_Syntax_Syntax.term) =
  fun g ->
    match g.FStarC_TypeChecker_Common.guard_f with
    | FStarC_TypeChecker_Common.Trivial -> FStarC_Syntax_Util.t_true
    | FStarC_TypeChecker_Common.NonTrivial f -> f
let (_t_trefl :
  Prims.bool ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term -> unit FStarC_Tactics_Monad.tac)
  =
  fun allow_guards ->
    fun l ->
      fun r ->
        let should_register_trefl g =
          let should_register = true in
          let skip_register = false in
          let uu___ =
            let uu___1 = FStarC_Options.compat_pre_core_should_register () in
            Prims.op_Negation uu___1 in
          if uu___
          then skip_register
          else
            (let is_uvar_untyped_or_already_checked u =
               let dec =
                 FStarC_Syntax_Unionfind.find_decoration
                   u.FStarC_Syntax_Syntax.ctx_uvar_head in
               match dec.FStarC_Syntax_Syntax.uvar_decoration_should_check
               with
               | FStarC_Syntax_Syntax.Allow_untyped uu___2 -> true
               | FStarC_Syntax_Syntax.Already_checked -> true
               | uu___2 -> false in
             let is_uvar t =
               let head = FStarC_Syntax_Util.leftmost_head t in
               let uu___2 =
                 let uu___3 = FStarC_Syntax_Subst.compress head in
                 uu___3.FStarC_Syntax_Syntax.n in
               match uu___2 with
               | FStarC_Syntax_Syntax.Tm_uvar (u, uu___3) ->
                   FStar_Pervasives.Inl (u, head, t)
               | uu___3 -> FStar_Pervasives.Inr t in
             let is_allow_untyped_uvar t =
               let uu___2 = is_uvar t in
               match uu___2 with
               | FStar_Pervasives.Inr uu___3 -> false
               | FStar_Pervasives.Inl (u, uu___3, uu___4) ->
                   is_uvar_untyped_or_already_checked u in
             let t =
               FStarC_Syntax_Util.ctx_uvar_typ
                 g.FStarC_Tactics_Types.goal_ctx_uvar in
             let uvars =
               let uu___2 = FStarC_Syntax_Free.uvars t in
               FStarC_Class_Setlike.elems ()
                 (Obj.magic
                    (FStarC_Compiler_FlatSet.setlike_flat_set
                       FStarC_Syntax_Free.ord_ctx_uvar)) (Obj.magic uu___2) in
             let uu___2 =
               FStarC_Compiler_Util.for_all
                 is_uvar_untyped_or_already_checked uvars in
             if uu___2
             then skip_register
             else
               (let uu___4 =
                  let t1 =
                    let uu___5 = FStarC_Syntax_Util.un_squash t in
                    match uu___5 with
                    | FStar_Pervasives_Native.None -> t
                    | FStar_Pervasives_Native.Some t2 -> t2 in
                  FStarC_Syntax_Util.leftmost_head_and_args t1 in
                match uu___4 with
                | (head, args) ->
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 = FStarC_Syntax_Util.un_uinst head in
                          FStarC_Syntax_Subst.compress uu___8 in
                        uu___7.FStarC_Syntax_Syntax.n in
                      (uu___6, args) in
                    (match uu___5 with
                     | (FStarC_Syntax_Syntax.Tm_fvar fv,
                        (ty, uu___6)::(t1, uu___7)::(t2, uu___8)::[]) when
                         FStarC_Syntax_Syntax.fv_eq_lid fv
                           FStarC_Parser_Const.eq2_lid
                         ->
                         let uu___9 =
                           (is_allow_untyped_uvar t1) ||
                             (is_allow_untyped_uvar t2) in
                         if uu___9
                         then skip_register
                         else
                           (let uu___11 =
                              FStarC_Tactics_Monad.is_goal_safe_as_well_typed
                                g in
                            if uu___11
                            then
                              let check_uvar_subtype u t3 =
                                let env1 =
                                  let uu___12 =
                                    FStarC_Tactics_Types.goal_env g in
                                  {
                                    FStarC_TypeChecker_Env.solver =
                                      (uu___12.FStarC_TypeChecker_Env.solver);
                                    FStarC_TypeChecker_Env.range =
                                      (uu___12.FStarC_TypeChecker_Env.range);
                                    FStarC_TypeChecker_Env.curmodule =
                                      (uu___12.FStarC_TypeChecker_Env.curmodule);
                                    FStarC_TypeChecker_Env.gamma =
                                      ((g.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_gamma);
                                    FStarC_TypeChecker_Env.gamma_sig =
                                      (uu___12.FStarC_TypeChecker_Env.gamma_sig);
                                    FStarC_TypeChecker_Env.gamma_cache =
                                      (uu___12.FStarC_TypeChecker_Env.gamma_cache);
                                    FStarC_TypeChecker_Env.modules =
                                      (uu___12.FStarC_TypeChecker_Env.modules);
                                    FStarC_TypeChecker_Env.expected_typ =
                                      (uu___12.FStarC_TypeChecker_Env.expected_typ);
                                    FStarC_TypeChecker_Env.sigtab =
                                      (uu___12.FStarC_TypeChecker_Env.sigtab);
                                    FStarC_TypeChecker_Env.attrtab =
                                      (uu___12.FStarC_TypeChecker_Env.attrtab);
                                    FStarC_TypeChecker_Env.instantiate_imp =
                                      (uu___12.FStarC_TypeChecker_Env.instantiate_imp);
                                    FStarC_TypeChecker_Env.effects =
                                      (uu___12.FStarC_TypeChecker_Env.effects);
                                    FStarC_TypeChecker_Env.generalize =
                                      (uu___12.FStarC_TypeChecker_Env.generalize);
                                    FStarC_TypeChecker_Env.letrecs =
                                      (uu___12.FStarC_TypeChecker_Env.letrecs);
                                    FStarC_TypeChecker_Env.top_level =
                                      (uu___12.FStarC_TypeChecker_Env.top_level);
                                    FStarC_TypeChecker_Env.check_uvars =
                                      (uu___12.FStarC_TypeChecker_Env.check_uvars);
                                    FStarC_TypeChecker_Env.use_eq_strict =
                                      (uu___12.FStarC_TypeChecker_Env.use_eq_strict);
                                    FStarC_TypeChecker_Env.is_iface =
                                      (uu___12.FStarC_TypeChecker_Env.is_iface);
                                    FStarC_TypeChecker_Env.admit =
                                      (uu___12.FStarC_TypeChecker_Env.admit);
                                    FStarC_TypeChecker_Env.lax_universes =
                                      (uu___12.FStarC_TypeChecker_Env.lax_universes);
                                    FStarC_TypeChecker_Env.phase1 =
                                      (uu___12.FStarC_TypeChecker_Env.phase1);
                                    FStarC_TypeChecker_Env.failhard =
                                      (uu___12.FStarC_TypeChecker_Env.failhard);
                                    FStarC_TypeChecker_Env.flychecking =
                                      (uu___12.FStarC_TypeChecker_Env.flychecking);
                                    FStarC_TypeChecker_Env.uvar_subtyping =
                                      (uu___12.FStarC_TypeChecker_Env.uvar_subtyping);
                                    FStarC_TypeChecker_Env.intactics =
                                      (uu___12.FStarC_TypeChecker_Env.intactics);
                                    FStarC_TypeChecker_Env.nocoerce =
                                      (uu___12.FStarC_TypeChecker_Env.nocoerce);
                                    FStarC_TypeChecker_Env.tc_term =
                                      (uu___12.FStarC_TypeChecker_Env.tc_term);
                                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                      =
                                      (uu___12.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                    FStarC_TypeChecker_Env.universe_of =
                                      (uu___12.FStarC_TypeChecker_Env.universe_of);
                                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                      =
                                      (uu___12.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                    FStarC_TypeChecker_Env.teq_nosmt_force =
                                      (uu___12.FStarC_TypeChecker_Env.teq_nosmt_force);
                                    FStarC_TypeChecker_Env.subtype_nosmt_force
                                      =
                                      (uu___12.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                    FStarC_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___12.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                    FStarC_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___12.FStarC_TypeChecker_Env.normalized_eff_names);
                                    FStarC_TypeChecker_Env.fv_delta_depths =
                                      (uu___12.FStarC_TypeChecker_Env.fv_delta_depths);
                                    FStarC_TypeChecker_Env.proof_ns =
                                      (uu___12.FStarC_TypeChecker_Env.proof_ns);
                                    FStarC_TypeChecker_Env.synth_hook =
                                      (uu___12.FStarC_TypeChecker_Env.synth_hook);
                                    FStarC_TypeChecker_Env.try_solve_implicits_hook
                                      =
                                      (uu___12.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                    FStarC_TypeChecker_Env.splice =
                                      (uu___12.FStarC_TypeChecker_Env.splice);
                                    FStarC_TypeChecker_Env.mpreprocess =
                                      (uu___12.FStarC_TypeChecker_Env.mpreprocess);
                                    FStarC_TypeChecker_Env.postprocess =
                                      (uu___12.FStarC_TypeChecker_Env.postprocess);
                                    FStarC_TypeChecker_Env.identifier_info =
                                      (uu___12.FStarC_TypeChecker_Env.identifier_info);
                                    FStarC_TypeChecker_Env.tc_hooks =
                                      (uu___12.FStarC_TypeChecker_Env.tc_hooks);
                                    FStarC_TypeChecker_Env.dsenv =
                                      (uu___12.FStarC_TypeChecker_Env.dsenv);
                                    FStarC_TypeChecker_Env.nbe =
                                      (uu___12.FStarC_TypeChecker_Env.nbe);
                                    FStarC_TypeChecker_Env.strict_args_tab =
                                      (uu___12.FStarC_TypeChecker_Env.strict_args_tab);
                                    FStarC_TypeChecker_Env.erasable_types_tab
                                      =
                                      (uu___12.FStarC_TypeChecker_Env.erasable_types_tab);
                                    FStarC_TypeChecker_Env.enable_defer_to_tac
                                      =
                                      (uu___12.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                    FStarC_TypeChecker_Env.unif_allow_ref_guards
                                      =
                                      (uu___12.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                    FStarC_TypeChecker_Env.erase_erasable_args
                                      =
                                      (uu___12.FStarC_TypeChecker_Env.erase_erasable_args);
                                    FStarC_TypeChecker_Env.core_check =
                                      (uu___12.FStarC_TypeChecker_Env.core_check);
                                    FStarC_TypeChecker_Env.missing_decl =
                                      (uu___12.FStarC_TypeChecker_Env.missing_decl)
                                  } in
                                let uu___12 =
                                  FStarC_TypeChecker_Core.compute_term_type_handle_guards
                                    env1 t3
                                    (fun uu___13 -> fun uu___14 -> true) in
                                match uu___12 with
                                | FStar_Pervasives.Inr uu___13 -> false
                                | FStar_Pervasives.Inl (uu___13, t_ty) ->
                                    let uu___14 =
                                      FStarC_TypeChecker_Core.check_term_subtyping
                                        true true env1 ty t_ty in
                                    (match uu___14 with
                                     | FStar_Pervasives.Inl
                                         (FStar_Pervasives_Native.None) ->
                                         (mark_uvar_as_already_checked u;
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
        FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
          (Obj.magic FStarC_Tactics_Monad.cur_goal)
          (fun uu___ ->
             (fun g ->
                let g = Obj.magic g in
                let should_check = should_check_goal_uvar g in
                (let uu___1 = should_register_trefl g in
                 if uu___1 then FStarC_Tactics_Monad.register_goal g else ());
                (let must_tot = true in
                 let attempt uu___2 uu___1 =
                   (fun l1 ->
                      fun r1 ->
                        let uu___1 =
                          let uu___2 = FStarC_Tactics_Types.goal_env g in
                          do_unify_maybe_guards allow_guards must_tot uu___2
                            l1 r1 in
                        Obj.magic
                          (FStarC_Class_Monad.op_let_Bang
                             FStarC_Tactics_Monad.monad_tac () ()
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                (fun uu___2 ->
                                   let uu___2 = Obj.magic uu___2 in
                                   match uu___2 with
                                   | FStar_Pervasives_Native.None ->
                                       Obj.magic (Obj.repr (ret false))
                                   | FStar_Pervasives_Native.Some guard ->
                                       Obj.magic
                                         (Obj.repr
                                            (let uu___3 =
                                               solve' g
                                                 FStarC_Syntax_Util.exp_unit in
                                             FStarC_Class_Monad.op_let_Bang
                                               FStarC_Tactics_Monad.monad_tac
                                               () () uu___3
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
                                                                 FStarC_Tactics_Types.goal_env
                                                                   g in
                                                               let uu___7 =
                                                                 guard_formula
                                                                   guard in
                                                               FStarC_Tactics_Monad.goal_of_guard
                                                                 "t_trefl"
                                                                 uu___6
                                                                 uu___7
                                                                 (FStar_Pervasives_Native.Some
                                                                    should_check)
                                                                 (rangeof g) in
                                                             FStarC_Class_Monad.op_let_Bang
                                                               FStarC_Tactics_Monad.monad_tac
                                                               () ()
                                                               (Obj.magic
                                                                  uu___5)
                                                               (fun uu___6 ->
                                                                  (fun goal
                                                                    ->
                                                                    let goal
                                                                    =
                                                                    Obj.magic
                                                                    goal in
                                                                    let uu___6
                                                                    =
                                                                    FStarC_Tactics_Monad.push_goals
                                                                    [goal] in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    (ret true))
                                                                    uu___7)))
                                                                    uu___6)))
                                                     else
                                                       Obj.magic
                                                         (Obj.repr
                                                            (let uu___6 =
                                                               FStarC_TypeChecker_Env.is_trivial_guard_formula
                                                                 guard in
                                                             if uu___6
                                                             then ret true
                                                             else
                                                               failwith
                                                                 "internal error: _t_refl: guard is not trivial")))
                                                    uu___4)))) uu___2)))
                     uu___2 uu___1 in
                 let uu___1 = attempt l r in
                 Obj.magic
                   (FStarC_Class_Monad.op_let_Bang
                      FStarC_Tactics_Monad.monad_tac () () (Obj.magic uu___1)
                      (fun uu___2 ->
                         (fun uu___2 ->
                            let uu___2 = Obj.magic uu___2 in
                            if uu___2
                            then Obj.magic (ret ())
                            else
                              (let norm1 =
                                 let uu___3 = FStarC_Tactics_Types.goal_env g in
                                 FStarC_TypeChecker_Normalize.normalize
                                   [FStarC_TypeChecker_Env.UnfoldUntil
                                      FStarC_Syntax_Syntax.delta_constant;
                                   FStarC_TypeChecker_Env.Primops;
                                   FStarC_TypeChecker_Env.DontUnfoldAttr
                                     [FStarC_Parser_Const.tac_opaque_attr]]
                                   uu___3 in
                               let uu___3 =
                                 let uu___4 = norm1 l in
                                 let uu___5 = norm1 r in
                                 attempt uu___4 uu___5 in
                               Obj.magic
                                 (FStarC_Class_Monad.op_let_Bang
                                    FStarC_Tactics_Monad.monad_tac () ()
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun uu___4 ->
                                          let uu___4 = Obj.magic uu___4 in
                                          if uu___4
                                          then Obj.magic (ret ())
                                          else
                                            (let uu___5 =
                                               let uu___6 =
                                                 let uu___7 =
                                                   FStarC_Tactics_Types.goal_env
                                                     g in
                                                 tts uu___7 in
                                               FStarC_TypeChecker_Err.print_discrepancy
                                                 uu___6 l r in
                                             match uu___5 with
                                             | (ls, rs) ->
                                                 Obj.magic
                                                   (fail2
                                                      "cannot unify (%s) and (%s)"
                                                      ls rs))) uu___4))))
                           uu___2)))) uu___)
let (t_trefl : Prims.bool -> unit FStarC_Tactics_Monad.tac) =
  fun allow_guards ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
            (Obj.magic FStarC_Tactics_Monad.cur_goal)
            (fun uu___3 ->
               (fun g ->
                  let g = Obj.magic g in
                  let uu___3 =
                    let uu___4 = FStarC_Tactics_Types.goal_env g in
                    let uu___5 = FStarC_Tactics_Types.goal_type g in
                    destruct_eq uu___4 uu___5 in
                  match uu___3 with
                  | FStar_Pervasives_Native.Some (l, r) ->
                      Obj.magic (_t_trefl allow_guards l r)
                  | FStar_Pervasives_Native.None ->
                      let uu___4 =
                        let uu___5 = FStarC_Tactics_Types.goal_env g in
                        let uu___6 = FStarC_Tactics_Types.goal_type g in
                        tts uu___5 uu___6 in
                      Obj.magic (fail1 "not an equality (%s)" uu___4)) uu___3) in
        FStarC_Tactics_Monad.catch uu___2 in
      FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
        (Obj.magic uu___1)
        (fun uu___2 ->
           (fun uu___2 ->
              let uu___2 = Obj.magic uu___2 in
              match uu___2 with
              | FStar_Pervasives.Inr v -> Obj.magic (ret ())
              | FStar_Pervasives.Inl exn ->
                  Obj.magic (FStarC_Tactics_Monad.traise exn)) uu___2) in
    FStarC_Tactics_Monad.wrap_err "t_trefl" uu___
let (dup : unit -> unit FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
      (Obj.magic FStarC_Tactics_Monad.cur_goal)
      (fun uu___1 ->
         (fun g ->
            let g = Obj.magic g in
            let goal_sc = should_check_goal_uvar g in
            let env1 = FStarC_Tactics_Types.goal_env g in
            let uu___1 =
              let uu___2 = FStarC_Tactics_Types.goal_type g in
              let uu___3 =
                let uu___4 = should_check_goal_uvar g in
                FStar_Pervasives_Native.Some uu___4 in
              let uu___4 = goal_typedness_deps g in
              FStarC_Tactics_Monad.new_uvar "dup" env1 uu___2 uu___3 uu___4
                (rangeof g) in
            Obj.magic
              (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac
                 () () (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun uu___2 ->
                       let uu___2 = Obj.magic uu___2 in
                       match uu___2 with
                       | (u, u_uvar) ->
                           (mark_uvar_as_already_checked
                              g.FStarC_Tactics_Types.goal_ctx_uvar;
                            (let g' =
                               {
                                 FStarC_Tactics_Types.goal_main_env =
                                   (g.FStarC_Tactics_Types.goal_main_env);
                                 FStarC_Tactics_Types.goal_ctx_uvar = u_uvar;
                                 FStarC_Tactics_Types.opts =
                                   (g.FStarC_Tactics_Types.opts);
                                 FStarC_Tactics_Types.is_guard =
                                   (g.FStarC_Tactics_Types.is_guard);
                                 FStarC_Tactics_Types.label =
                                   (g.FStarC_Tactics_Types.label)
                               } in
                             Obj.magic
                               (FStarC_Class_Monad.op_let_Bang
                                  FStarC_Tactics_Monad.monad_tac () ()
                                  FStarC_Tactics_Monad.dismiss
                                  (fun uu___4 ->
                                     (fun uu___4 ->
                                        let uu___4 = Obj.magic uu___4 in
                                        let t_eq =
                                          let uu___5 =
                                            let uu___6 =
                                              FStarC_Tactics_Types.goal_type
                                                g in
                                            env1.FStarC_TypeChecker_Env.universe_of
                                              env1 uu___6 in
                                          let uu___6 =
                                            FStarC_Tactics_Types.goal_type g in
                                          let uu___7 =
                                            FStarC_Tactics_Types.goal_witness
                                              g in
                                          FStarC_Syntax_Util.mk_eq2 uu___5
                                            uu___6 u uu___7 in
                                        let uu___5 =
                                          FStarC_Tactics_Monad.add_irrelevant_goal
                                            g "dup equation" env1 t_eq
                                            (FStar_Pervasives_Native.Some
                                               goal_sc) in
                                        Obj.magic
                                          (FStarC_Class_Monad.op_let_Bang
                                             FStarC_Tactics_Monad.monad_tac
                                             () () uu___5
                                             (fun uu___6 ->
                                                (fun uu___6 ->
                                                   let uu___6 =
                                                     Obj.magic uu___6 in
                                                   Obj.magic
                                                     (FStarC_Tactics_Monad.add_goals
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
        | (pr, t1, t2) -> ((FStarC_Compiler_List.rev pr), t1, t2)
let (eq_binding :
  FStarC_Syntax_Syntax.binding -> FStarC_Syntax_Syntax.binding -> Prims.bool)
  =
  fun b1 ->
    fun b2 ->
      match (b1, b2) with
      | (FStarC_Syntax_Syntax.Binding_var bv1,
         FStarC_Syntax_Syntax.Binding_var bv2) ->
          (FStarC_Syntax_Syntax.bv_eq bv1 bv2) &&
            (FStarC_Syntax_Util.term_eq bv1.FStarC_Syntax_Syntax.sort
               bv2.FStarC_Syntax_Syntax.sort)
      | (FStarC_Syntax_Syntax.Binding_lid (lid1, uu___),
         FStarC_Syntax_Syntax.Binding_lid (lid2, uu___1)) ->
          FStarC_Ident.lid_equals lid1 lid2
      | (FStarC_Syntax_Syntax.Binding_univ u1,
         FStarC_Syntax_Syntax.Binding_univ u2) ->
          FStarC_Ident.ident_equals u1 u2
      | uu___ -> false
let (join_goals :
  FStarC_Tactics_Types.goal ->
    FStarC_Tactics_Types.goal ->
      FStarC_Tactics_Types.goal FStarC_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g1 ->
         fun g2 ->
           let close_forall_no_univs bs f =
             FStarC_Compiler_List.fold_right
               (fun b ->
                  fun f1 ->
                    FStarC_Syntax_Util.mk_forall_no_univ
                      b.FStarC_Syntax_Syntax.binder_bv f1) bs f in
           let uu___ = get_phi g1 in
           match uu___ with
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (FStarC_Tactics_Monad.fail "goal 1 is not irrelevant"))
           | FStar_Pervasives_Native.Some phi1 ->
               Obj.magic
                 (Obj.repr
                    (let uu___1 = get_phi g2 in
                     match uu___1 with
                     | FStar_Pervasives_Native.None ->
                         Obj.repr
                           (FStarC_Tactics_Monad.fail
                              "goal 2 is not irrelevant")
                     | FStar_Pervasives_Native.Some phi2 ->
                         Obj.repr
                           (let gamma1 =
                              (g1.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_gamma in
                            let gamma2 =
                              (g2.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_gamma in
                            let uu___2 =
                              longest_prefix eq_binding
                                (FStarC_Compiler_List.rev gamma1)
                                (FStarC_Compiler_List.rev gamma2) in
                            match uu___2 with
                            | (gamma, r1, r2) ->
                                let t1 =
                                  let uu___3 =
                                    FStarC_TypeChecker_Env.binders_of_bindings
                                      (FStarC_Compiler_List.rev r1) in
                                  close_forall_no_univs uu___3 phi1 in
                                let t2 =
                                  let uu___3 =
                                    FStarC_TypeChecker_Env.binders_of_bindings
                                      (FStarC_Compiler_List.rev r2) in
                                  close_forall_no_univs uu___3 phi2 in
                                let goal_sc =
                                  let uu___3 =
                                    let uu___4 = should_check_goal_uvar g1 in
                                    let uu___5 = should_check_goal_uvar g2 in
                                    (uu___4, uu___5) in
                                  match uu___3 with
                                  | (FStarC_Syntax_Syntax.Allow_untyped
                                     reason1,
                                     FStarC_Syntax_Syntax.Allow_untyped
                                     uu___4) ->
                                      FStar_Pervasives_Native.Some
                                        (FStarC_Syntax_Syntax.Allow_untyped
                                           reason1)
                                  | uu___4 -> FStar_Pervasives_Native.None in
                                let uu___3 =
                                  set_solution g1 FStarC_Syntax_Util.exp_unit in
                                FStarC_Class_Monad.op_let_Bang
                                  FStarC_Tactics_Monad.monad_tac () () uu___3
                                  (fun uu___4 ->
                                     (fun uu___4 ->
                                        let uu___4 = Obj.magic uu___4 in
                                        let uu___5 =
                                          set_solution g2
                                            FStarC_Syntax_Util.exp_unit in
                                        Obj.magic
                                          (FStarC_Class_Monad.op_let_Bang
                                             FStarC_Tactics_Monad.monad_tac
                                             () () uu___5
                                             (fun uu___6 ->
                                                (fun uu___6 ->
                                                   let uu___6 =
                                                     Obj.magic uu___6 in
                                                   let ng =
                                                     FStarC_Syntax_Util.mk_conj
                                                       t1 t2 in
                                                   let nenv =
                                                     let uu___7 =
                                                       FStarC_Tactics_Types.goal_env
                                                         g1 in
                                                     {
                                                       FStarC_TypeChecker_Env.solver
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.solver);
                                                       FStarC_TypeChecker_Env.range
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.range);
                                                       FStarC_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.curmodule);
                                                       FStarC_TypeChecker_Env.gamma
                                                         =
                                                         (FStarC_Compiler_List.rev
                                                            gamma);
                                                       FStarC_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.gamma_sig);
                                                       FStarC_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.gamma_cache);
                                                       FStarC_TypeChecker_Env.modules
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.modules);
                                                       FStarC_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.expected_typ);
                                                       FStarC_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.sigtab);
                                                       FStarC_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.attrtab);
                                                       FStarC_TypeChecker_Env.instantiate_imp
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.instantiate_imp);
                                                       FStarC_TypeChecker_Env.effects
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.effects);
                                                       FStarC_TypeChecker_Env.generalize
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.generalize);
                                                       FStarC_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.letrecs);
                                                       FStarC_TypeChecker_Env.top_level
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.top_level);
                                                       FStarC_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.check_uvars);
                                                       FStarC_TypeChecker_Env.use_eq_strict
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.use_eq_strict);
                                                       FStarC_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.is_iface);
                                                       FStarC_TypeChecker_Env.admit
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.admit);
                                                       FStarC_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.lax_universes);
                                                       FStarC_TypeChecker_Env.phase1
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.phase1);
                                                       FStarC_TypeChecker_Env.failhard
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.failhard);
                                                       FStarC_TypeChecker_Env.flychecking
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.flychecking);
                                                       FStarC_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.uvar_subtyping);
                                                       FStarC_TypeChecker_Env.intactics
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.intactics);
                                                       FStarC_TypeChecker_Env.nocoerce
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.nocoerce);
                                                       FStarC_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.tc_term);
                                                       FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                                       FStarC_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.universe_of);
                                                       FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                                       FStarC_TypeChecker_Env.teq_nosmt_force
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.teq_nosmt_force);
                                                       FStarC_TypeChecker_Env.subtype_nosmt_force
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                                       FStarC_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                                       FStarC_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.normalized_eff_names);
                                                       FStarC_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.fv_delta_depths);
                                                       FStarC_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.proof_ns);
                                                       FStarC_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.synth_hook);
                                                       FStarC_TypeChecker_Env.try_solve_implicits_hook
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                                       FStarC_TypeChecker_Env.splice
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.splice);
                                                       FStarC_TypeChecker_Env.mpreprocess
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.mpreprocess);
                                                       FStarC_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.postprocess);
                                                       FStarC_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.identifier_info);
                                                       FStarC_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.tc_hooks);
                                                       FStarC_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.dsenv);
                                                       FStarC_TypeChecker_Env.nbe
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.nbe);
                                                       FStarC_TypeChecker_Env.strict_args_tab
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.strict_args_tab);
                                                       FStarC_TypeChecker_Env.erasable_types_tab
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.erasable_types_tab);
                                                       FStarC_TypeChecker_Env.enable_defer_to_tac
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                                       FStarC_TypeChecker_Env.unif_allow_ref_guards
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                                       FStarC_TypeChecker_Env.erase_erasable_args
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.erase_erasable_args);
                                                       FStarC_TypeChecker_Env.core_check
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.core_check);
                                                       FStarC_TypeChecker_Env.missing_decl
                                                         =
                                                         (uu___7.FStarC_TypeChecker_Env.missing_decl)
                                                     } in
                                                   let uu___7 =
                                                     FStarC_Tactics_Monad.mk_irrelevant_goal
                                                       "joined" nenv ng
                                                       goal_sc (rangeof g1)
                                                       g1.FStarC_Tactics_Types.opts
                                                       g1.FStarC_Tactics_Types.label in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_let_Bang
                                                        FStarC_Tactics_Monad.monad_tac
                                                        () ()
                                                        (Obj.magic uu___7)
                                                        (fun uu___8 ->
                                                           (fun goal ->
                                                              let goal =
                                                                Obj.magic
                                                                  goal in
                                                              let uu___8 =
                                                                FStarC_Tactics_Monad.if_verbose
                                                                  (fun uu___9
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    FStarC_Tactics_Printing.goal_to_string_verbose
                                                                    g1 in
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Tactics_Printing.goal_to_string_verbose
                                                                    g2 in
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Tactics_Printing.goal_to_string_verbose
                                                                    goal in
                                                                    FStarC_Compiler_Util.print3
                                                                    "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                                                    uu___10
                                                                    uu___11
                                                                    uu___12) in
                                                              Obj.magic
                                                                (FStarC_Class_Monad.op_let_Bang
                                                                   FStarC_Tactics_Monad.monad_tac
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
                                                                    (ret goal))
                                                                    uu___9)))
                                                             uu___8))) uu___6)))
                                       uu___4))))) uu___1 uu___
let (join : unit -> unit FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
      (Obj.magic FStarC_Tactics_Monad.get)
      (fun uu___1 ->
         (fun ps ->
            let ps = Obj.magic ps in
            match ps.FStarC_Tactics_Types.goals with
            | g1::g2::gs ->
                let uu___1 =
                  FStarC_Tactics_Monad.set
                    {
                      FStarC_Tactics_Types.main_context =
                        (ps.FStarC_Tactics_Types.main_context);
                      FStarC_Tactics_Types.all_implicits =
                        (ps.FStarC_Tactics_Types.all_implicits);
                      FStarC_Tactics_Types.goals = gs;
                      FStarC_Tactics_Types.smt_goals =
                        (ps.FStarC_Tactics_Types.smt_goals);
                      FStarC_Tactics_Types.depth =
                        (ps.FStarC_Tactics_Types.depth);
                      FStarC_Tactics_Types.__dump =
                        (ps.FStarC_Tactics_Types.__dump);
                      FStarC_Tactics_Types.psc =
                        (ps.FStarC_Tactics_Types.psc);
                      FStarC_Tactics_Types.entry_range =
                        (ps.FStarC_Tactics_Types.entry_range);
                      FStarC_Tactics_Types.guard_policy =
                        (ps.FStarC_Tactics_Types.guard_policy);
                      FStarC_Tactics_Types.freshness =
                        (ps.FStarC_Tactics_Types.freshness);
                      FStarC_Tactics_Types.tac_verb_dbg =
                        (ps.FStarC_Tactics_Types.tac_verb_dbg);
                      FStarC_Tactics_Types.local_state =
                        (ps.FStarC_Tactics_Types.local_state);
                      FStarC_Tactics_Types.urgency =
                        (ps.FStarC_Tactics_Types.urgency);
                      FStarC_Tactics_Types.dump_on_failure =
                        (ps.FStarC_Tactics_Types.dump_on_failure)
                    } in
                Obj.magic
                  (FStarC_Class_Monad.op_let_Bang
                     FStarC_Tactics_Monad.monad_tac () () uu___1
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___2 = Obj.magic uu___2 in
                           let uu___3 = join_goals g1 g2 in
                           Obj.magic
                             (FStarC_Class_Monad.op_let_Bang
                                FStarC_Tactics_Monad.monad_tac () ()
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun g12 ->
                                      let g12 = Obj.magic g12 in
                                      Obj.magic
                                        (FStarC_Tactics_Monad.add_goals [g12]))
                                     uu___4))) uu___2))
            | uu___1 ->
                Obj.magic
                  (FStarC_Tactics_Monad.fail "join: less than 2 goals"))
           uu___1)
let (set_options : Prims.string -> unit FStarC_Tactics_Monad.tac) =
  fun s ->
    let uu___ =
      FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
        (Obj.magic FStarC_Tactics_Monad.cur_goal)
        (fun uu___1 ->
           (fun g ->
              let g = Obj.magic g in
              FStarC_Options.push ();
              FStarC_Options.set g.FStarC_Tactics_Types.opts;
              (let res = FStarC_Options.set_options s in
               let opts' = FStarC_Options.peek () in
               FStarC_Options.pop ();
               (match res with
                | FStarC_Getopt.Success ->
                    let g' =
                      {
                        FStarC_Tactics_Types.goal_main_env =
                          (g.FStarC_Tactics_Types.goal_main_env);
                        FStarC_Tactics_Types.goal_ctx_uvar =
                          (g.FStarC_Tactics_Types.goal_ctx_uvar);
                        FStarC_Tactics_Types.opts = opts';
                        FStarC_Tactics_Types.is_guard =
                          (g.FStarC_Tactics_Types.is_guard);
                        FStarC_Tactics_Types.label =
                          (g.FStarC_Tactics_Types.label)
                      } in
                    Obj.magic (FStarC_Tactics_Monad.replace_cur g')
                | FStarC_Getopt.Error err ->
                    Obj.magic (fail2 "Setting options `%s` failed: %s" s err)
                | FStarC_Getopt.Help ->
                    Obj.magic
                      (fail1 "Setting options `%s` failed (got `Help`?)" s))))
             uu___1) in
    FStarC_Tactics_Monad.wrap_err "set_options" uu___
let (top_env : unit -> env FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 = bind () in
    uu___1 FStarC_Tactics_Monad.get
      (fun ps -> ret ps.FStarC_Tactics_Types.main_context)
let (lax_on : unit -> Prims.bool FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
            (Obj.magic FStarC_Tactics_Monad.cur_goal)
            (fun uu___1 ->
               (fun g ->
                  let g = Obj.magic g in
                  let uu___1 =
                    (FStarC_Options.lax ()) ||
                      (let uu___2 = FStarC_Tactics_Types.goal_env g in
                       uu___2.FStarC_TypeChecker_Env.admit) in
                  Obj.magic (ret uu___1)) uu___1))) uu___
let (unquote :
  FStarC_Syntax_Syntax.typ ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term FStarC_Tactics_Monad.tac)
  =
  fun ty ->
    fun tm ->
      let uu___ =
        let uu___1 =
          FStarC_Tactics_Monad.if_verbose
            (fun uu___2 ->
               let uu___3 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tm in
               FStarC_Compiler_Util.print1 "unquote: tm = %s\n" uu___3) in
        Obj.magic
          (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac ()
             () uu___1
             (fun uu___2 ->
                (fun uu___2 ->
                   let uu___2 = Obj.magic uu___2 in
                   Obj.magic
                     (FStarC_Class_Monad.op_let_Bang
                        FStarC_Tactics_Monad.monad_tac () ()
                        (Obj.magic FStarC_Tactics_Monad.cur_goal)
                        (fun uu___3 ->
                           (fun goal ->
                              let goal = Obj.magic goal in
                              let env1 =
                                let uu___3 =
                                  FStarC_Tactics_Types.goal_env goal in
                                FStarC_TypeChecker_Env.set_expected_typ
                                  uu___3 ty in
                              let uu___3 = __tc_ghost env1 tm in
                              Obj.magic
                                (FStarC_Class_Monad.op_let_Bang
                                   FStarC_Tactics_Monad.monad_tac () ()
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun uu___4 ->
                                         let uu___4 = Obj.magic uu___4 in
                                         match uu___4 with
                                         | (tm1, typ, guard) ->
                                             let uu___5 =
                                               FStarC_Tactics_Monad.if_verbose
                                                 (fun uu___6 ->
                                                    let uu___7 =
                                                      FStarC_Class_Show.show
                                                        FStarC_Syntax_Print.showable_term
                                                        tm1 in
                                                    FStarC_Compiler_Util.print1
                                                      "unquote: tm' = %s\n"
                                                      uu___7) in
                                             Obj.magic
                                               (FStarC_Class_Monad.op_let_Bang
                                                  FStarC_Tactics_Monad.monad_tac
                                                  () () uu___5
                                                  (fun uu___6 ->
                                                     (fun uu___6 ->
                                                        let uu___6 =
                                                          Obj.magic uu___6 in
                                                        let uu___7 =
                                                          FStarC_Tactics_Monad.if_verbose
                                                            (fun uu___8 ->
                                                               let uu___9 =
                                                                 FStarC_Class_Show.show
                                                                   FStarC_Syntax_Print.showable_term
                                                                   typ in
                                                               FStarC_Compiler_Util.print1
                                                                 "unquote: typ = %s\n"
                                                                 uu___9) in
                                                        Obj.magic
                                                          (FStarC_Class_Monad.op_let_Bang
                                                             FStarC_Tactics_Monad.monad_tac
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
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    (ret tm1))
                                                                    uu___10)))
                                                                  uu___8)))
                                                       uu___6))) uu___4)))
                             uu___3))) uu___2)) in
      FStarC_Tactics_Monad.wrap_err "unquote" uu___
let (uvar_env :
  env ->
    FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStarC_Syntax_Syntax.term FStarC_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env1 ->
         fun ty ->
           Obj.magic
             (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac
                () () (Obj.magic FStarC_Tactics_Monad.get)
                (fun uu___ ->
                   (fun ps ->
                      let ps = Obj.magic ps in
                      let uu___ =
                        match ty with
                        | FStar_Pervasives_Native.Some ty1 ->
                            let env2 =
                              let uu___1 =
                                let uu___2 = FStarC_Syntax_Util.type_u () in
                                FStar_Pervasives_Native.fst uu___2 in
                              FStarC_TypeChecker_Env.set_expected_typ env1
                                uu___1 in
                            let uu___1 = __tc_ghost env2 ty1 in
                            Obj.magic
                              (FStarC_Class_Monad.op_let_Bang
                                 FStarC_Tactics_Monad.monad_tac () ()
                                 (Obj.magic uu___1)
                                 (fun uu___2 ->
                                    (fun uu___2 ->
                                       let uu___2 = Obj.magic uu___2 in
                                       match uu___2 with
                                       | (ty2, uu___3, g) ->
                                           Obj.magic
                                             (ret
                                                (ty2, g,
                                                  (ty2.FStarC_Syntax_Syntax.pos))))
                                      uu___2))
                        | FStar_Pervasives_Native.None ->
                            let uu___1 =
                              let uu___2 =
                                let uu___3 = FStarC_Syntax_Util.type_u () in
                                FStar_Pervasives_Native.fst uu___3 in
                              FStarC_Tactics_Monad.new_uvar "uvar_env.2" env1
                                uu___2 FStar_Pervasives_Native.None []
                                ps.FStarC_Tactics_Types.entry_range in
                            Obj.magic
                              (FStarC_Class_Monad.op_let_Bang
                                 FStarC_Tactics_Monad.monad_tac () ()
                                 (Obj.magic uu___1)
                                 (fun uu___2 ->
                                    (fun uu___2 ->
                                       let uu___2 = Obj.magic uu___2 in
                                       match uu___2 with
                                       | (typ, uvar_typ) ->
                                           Obj.magic
                                             (ret
                                                (typ,
                                                  FStarC_TypeChecker_Env.trivial_guard,
                                                  FStarC_Compiler_Range_Type.dummyRange)))
                                      uu___2)) in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Tactics_Monad.monad_tac () ()
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
                                       (FStarC_Class_Monad.op_let_Bang
                                          FStarC_Tactics_Monad.monad_tac ()
                                          () uu___2
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                let uu___3 = Obj.magic uu___3 in
                                                let uu___4 =
                                                  FStarC_Tactics_Monad.new_uvar
                                                    "uvar_env" env1 typ
                                                    FStar_Pervasives_Native.None
                                                    []
                                                    ps.FStarC_Tactics_Types.entry_range in
                                                Obj.magic
                                                  (FStarC_Class_Monad.op_let_Bang
                                                     FStarC_Tactics_Monad.monad_tac
                                                     () () (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        (fun uu___5 ->
                                                           let uu___5 =
                                                             Obj.magic uu___5 in
                                                           match uu___5 with
                                                           | (t, uvar_t) ->
                                                               Obj.magic
                                                                 (ret t))
                                                          uu___5))) uu___3)))
                                uu___1))) uu___))) uu___1 uu___
let (ghost_uvar_env :
  env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.term FStarC_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env1 ->
         fun ty ->
           Obj.magic
             (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac
                () () (Obj.magic FStarC_Tactics_Monad.get)
                (fun uu___ ->
                   (fun ps ->
                      let ps = Obj.magic ps in
                      let uu___ = __tc_ghost env1 ty in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Tactics_Monad.monad_tac () ()
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 let uu___1 = Obj.magic uu___1 in
                                 match uu___1 with
                                 | (typ, uu___2, g) ->
                                     let uu___3 =
                                       proc_guard "ghost_uvar_env_typ" env1 g
                                         FStar_Pervasives_Native.None
                                         ty.FStarC_Syntax_Syntax.pos in
                                     Obj.magic
                                       (FStarC_Class_Monad.op_let_Bang
                                          FStarC_Tactics_Monad.monad_tac ()
                                          () uu___3
                                          (fun uu___4 ->
                                             (fun uu___4 ->
                                                let uu___4 = Obj.magic uu___4 in
                                                let uu___5 =
                                                  FStarC_Tactics_Monad.new_uvar
                                                    "uvar_env" env1 typ
                                                    (FStar_Pervasives_Native.Some
                                                       (FStarC_Syntax_Syntax.Allow_ghost
                                                          "User ghost uvar"))
                                                    []
                                                    ps.FStarC_Tactics_Types.entry_range in
                                                Obj.magic
                                                  (FStarC_Class_Monad.op_let_Bang
                                                     FStarC_Tactics_Monad.monad_tac
                                                     () () (Obj.magic uu___5)
                                                     (fun uu___6 ->
                                                        (fun uu___6 ->
                                                           let uu___6 =
                                                             Obj.magic uu___6 in
                                                           match uu___6 with
                                                           | (t, uvar_t) ->
                                                               Obj.magic
                                                                 (ret t))
                                                          uu___6))) uu___4)))
                                uu___1))) uu___))) uu___1 uu___
let (fresh_universe_uvar :
  unit -> FStarC_Syntax_Syntax.term FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStarC_Syntax_Util.type_u () in
      FStar_Pervasives_Native.fst uu___2 in
    ret uu___1
let (unshelve : FStarC_Syntax_Syntax.term -> unit FStarC_Tactics_Monad.tac) =
  fun t ->
    let uu___ =
      FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
        (Obj.magic FStarC_Tactics_Monad.get)
        (fun uu___1 ->
           (fun ps ->
              let ps = Obj.magic ps in
              let env1 = ps.FStarC_Tactics_Types.main_context in
              let opts =
                match ps.FStarC_Tactics_Types.goals with
                | g::uu___1 -> g.FStarC_Tactics_Types.opts
                | uu___1 -> FStarC_Options.peek () in
              let uu___1 = FStarC_Syntax_Util.head_and_args t in
              match uu___1 with
              | ({
                   FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_uvar
                     (ctx_uvar, uu___2);
                   FStarC_Syntax_Syntax.pos = uu___3;
                   FStarC_Syntax_Syntax.vars = uu___4;
                   FStarC_Syntax_Syntax.hash_code = uu___5;_},
                 uu___6) ->
                  let env2 =
                    {
                      FStarC_TypeChecker_Env.solver =
                        (env1.FStarC_TypeChecker_Env.solver);
                      FStarC_TypeChecker_Env.range =
                        (env1.FStarC_TypeChecker_Env.range);
                      FStarC_TypeChecker_Env.curmodule =
                        (env1.FStarC_TypeChecker_Env.curmodule);
                      FStarC_TypeChecker_Env.gamma =
                        (ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_gamma);
                      FStarC_TypeChecker_Env.gamma_sig =
                        (env1.FStarC_TypeChecker_Env.gamma_sig);
                      FStarC_TypeChecker_Env.gamma_cache =
                        (env1.FStarC_TypeChecker_Env.gamma_cache);
                      FStarC_TypeChecker_Env.modules =
                        (env1.FStarC_TypeChecker_Env.modules);
                      FStarC_TypeChecker_Env.expected_typ =
                        (env1.FStarC_TypeChecker_Env.expected_typ);
                      FStarC_TypeChecker_Env.sigtab =
                        (env1.FStarC_TypeChecker_Env.sigtab);
                      FStarC_TypeChecker_Env.attrtab =
                        (env1.FStarC_TypeChecker_Env.attrtab);
                      FStarC_TypeChecker_Env.instantiate_imp =
                        (env1.FStarC_TypeChecker_Env.instantiate_imp);
                      FStarC_TypeChecker_Env.effects =
                        (env1.FStarC_TypeChecker_Env.effects);
                      FStarC_TypeChecker_Env.generalize =
                        (env1.FStarC_TypeChecker_Env.generalize);
                      FStarC_TypeChecker_Env.letrecs =
                        (env1.FStarC_TypeChecker_Env.letrecs);
                      FStarC_TypeChecker_Env.top_level =
                        (env1.FStarC_TypeChecker_Env.top_level);
                      FStarC_TypeChecker_Env.check_uvars =
                        (env1.FStarC_TypeChecker_Env.check_uvars);
                      FStarC_TypeChecker_Env.use_eq_strict =
                        (env1.FStarC_TypeChecker_Env.use_eq_strict);
                      FStarC_TypeChecker_Env.is_iface =
                        (env1.FStarC_TypeChecker_Env.is_iface);
                      FStarC_TypeChecker_Env.admit =
                        (env1.FStarC_TypeChecker_Env.admit);
                      FStarC_TypeChecker_Env.lax_universes =
                        (env1.FStarC_TypeChecker_Env.lax_universes);
                      FStarC_TypeChecker_Env.phase1 =
                        (env1.FStarC_TypeChecker_Env.phase1);
                      FStarC_TypeChecker_Env.failhard =
                        (env1.FStarC_TypeChecker_Env.failhard);
                      FStarC_TypeChecker_Env.flychecking =
                        (env1.FStarC_TypeChecker_Env.flychecking);
                      FStarC_TypeChecker_Env.uvar_subtyping =
                        (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                      FStarC_TypeChecker_Env.intactics =
                        (env1.FStarC_TypeChecker_Env.intactics);
                      FStarC_TypeChecker_Env.nocoerce =
                        (env1.FStarC_TypeChecker_Env.nocoerce);
                      FStarC_TypeChecker_Env.tc_term =
                        (env1.FStarC_TypeChecker_Env.tc_term);
                      FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                        (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                      FStarC_TypeChecker_Env.universe_of =
                        (env1.FStarC_TypeChecker_Env.universe_of);
                      FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                        =
                        (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                      FStarC_TypeChecker_Env.teq_nosmt_force =
                        (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                      FStarC_TypeChecker_Env.subtype_nosmt_force =
                        (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                      FStarC_TypeChecker_Env.qtbl_name_and_index =
                        (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                      FStarC_TypeChecker_Env.normalized_eff_names =
                        (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                      FStarC_TypeChecker_Env.fv_delta_depths =
                        (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                      FStarC_TypeChecker_Env.proof_ns =
                        (env1.FStarC_TypeChecker_Env.proof_ns);
                      FStarC_TypeChecker_Env.synth_hook =
                        (env1.FStarC_TypeChecker_Env.synth_hook);
                      FStarC_TypeChecker_Env.try_solve_implicits_hook =
                        (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                      FStarC_TypeChecker_Env.splice =
                        (env1.FStarC_TypeChecker_Env.splice);
                      FStarC_TypeChecker_Env.mpreprocess =
                        (env1.FStarC_TypeChecker_Env.mpreprocess);
                      FStarC_TypeChecker_Env.postprocess =
                        (env1.FStarC_TypeChecker_Env.postprocess);
                      FStarC_TypeChecker_Env.identifier_info =
                        (env1.FStarC_TypeChecker_Env.identifier_info);
                      FStarC_TypeChecker_Env.tc_hooks =
                        (env1.FStarC_TypeChecker_Env.tc_hooks);
                      FStarC_TypeChecker_Env.dsenv =
                        (env1.FStarC_TypeChecker_Env.dsenv);
                      FStarC_TypeChecker_Env.nbe =
                        (env1.FStarC_TypeChecker_Env.nbe);
                      FStarC_TypeChecker_Env.strict_args_tab =
                        (env1.FStarC_TypeChecker_Env.strict_args_tab);
                      FStarC_TypeChecker_Env.erasable_types_tab =
                        (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                      FStarC_TypeChecker_Env.enable_defer_to_tac =
                        (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                      FStarC_TypeChecker_Env.unif_allow_ref_guards =
                        (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                      FStarC_TypeChecker_Env.erase_erasable_args =
                        (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                      FStarC_TypeChecker_Env.core_check =
                        (env1.FStarC_TypeChecker_Env.core_check);
                      FStarC_TypeChecker_Env.missing_decl =
                        (env1.FStarC_TypeChecker_Env.missing_decl)
                    } in
                  let g =
                    FStarC_Tactics_Types.mk_goal env2 ctx_uvar opts false "" in
                  let g1 = bnorm_goal g in
                  Obj.magic (FStarC_Tactics_Monad.add_goals [g1])
              | uu___2 -> Obj.magic (FStarC_Tactics_Monad.fail "not a uvar"))
             uu___1) in
    FStarC_Tactics_Monad.wrap_err "unshelve" uu___
let (tac_and :
  Prims.bool FStarC_Tactics_Monad.tac ->
    Prims.bool FStarC_Tactics_Monad.tac ->
      Prims.bool FStarC_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t1 ->
         fun t2 ->
           Obj.magic
             (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac
                () () (Obj.magic t1)
                (fun uu___ ->
                   (fun uu___ ->
                      let uu___ = Obj.magic uu___ in
                      if uu___
                      then Obj.magic (Obj.repr t2)
                      else
                        Obj.magic
                          (Obj.repr
                             (FStarC_Class_Monad.return
                                FStarC_Tactics_Monad.monad_tac ()
                                (Obj.magic false)))) uu___))) uu___1 uu___
let default_if_err :
  'a . 'a -> 'a FStarC_Tactics_Monad.tac -> 'a FStarC_Tactics_Monad.tac =
  fun uu___1 ->
    fun uu___ ->
      (fun def ->
         fun t ->
           let uu___ = FStarC_Tactics_Monad.catch t in
           Obj.magic
             (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac
                () () (Obj.magic uu___)
                (fun uu___1 ->
                   (fun r ->
                      let r = Obj.magic r in
                      match r with
                      | FStar_Pervasives.Inl uu___1 ->
                          Obj.magic
                            (FStarC_Class_Monad.return
                               FStarC_Tactics_Monad.monad_tac ()
                               (Obj.magic def))
                      | FStar_Pervasives.Inr v ->
                          Obj.magic
                            (FStarC_Class_Monad.return
                               FStarC_Tactics_Monad.monad_tac ()
                               (Obj.magic v))) uu___1))) uu___1 uu___
let (match_env :
  env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term -> Prims.bool FStarC_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          Obj.magic
            (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac ()
               () (Obj.magic FStarC_Tactics_Monad.get)
               (fun uu___1 ->
                  (fun ps ->
                     let ps = Obj.magic ps in
                     let uu___1 = __tc e t1 in
                     Obj.magic
                       (FStarC_Class_Monad.op_let_Bang
                          FStarC_Tactics_Monad.monad_tac () ()
                          (Obj.magic uu___1)
                          (fun uu___2 ->
                             (fun uu___2 ->
                                let uu___2 = Obj.magic uu___2 in
                                match uu___2 with
                                | (t11, ty1, g1) ->
                                    let uu___3 = __tc e t2 in
                                    Obj.magic
                                      (FStarC_Class_Monad.op_let_Bang
                                         FStarC_Tactics_Monad.monad_tac () ()
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
                                                       ps.FStarC_Tactics_Types.entry_range in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_let_Bang
                                                        FStarC_Tactics_Monad.monad_tac
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
                                                                  ps.FStarC_Tactics_Types.entry_range in
                                                              Obj.magic
                                                                (FStarC_Class_Monad.op_let_Bang
                                                                   FStarC_Tactics_Monad.monad_tac
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
        FStarC_Tactics_Monad.wrap_err "match_env" uu___
let (unify_env :
  env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term -> Prims.bool FStarC_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          Obj.magic
            (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac ()
               () (Obj.magic FStarC_Tactics_Monad.get)
               (fun uu___1 ->
                  (fun ps ->
                     let ps = Obj.magic ps in
                     let uu___1 = __tc e t1 in
                     Obj.magic
                       (FStarC_Class_Monad.op_let_Bang
                          FStarC_Tactics_Monad.monad_tac () ()
                          (Obj.magic uu___1)
                          (fun uu___2 ->
                             (fun uu___2 ->
                                let uu___2 = Obj.magic uu___2 in
                                match uu___2 with
                                | (t11, ty1, g1) ->
                                    let uu___3 = __tc e t2 in
                                    Obj.magic
                                      (FStarC_Class_Monad.op_let_Bang
                                         FStarC_Tactics_Monad.monad_tac () ()
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
                                                       ps.FStarC_Tactics_Types.entry_range in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_let_Bang
                                                        FStarC_Tactics_Monad.monad_tac
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
                                                                  ps.FStarC_Tactics_Types.entry_range in
                                                              Obj.magic
                                                                (FStarC_Class_Monad.op_let_Bang
                                                                   FStarC_Tactics_Monad.monad_tac
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
        FStarC_Tactics_Monad.wrap_err "unify_env" uu___
let (unify_guard_env :
  env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term -> Prims.bool FStarC_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          Obj.magic
            (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac ()
               () (Obj.magic FStarC_Tactics_Monad.get)
               (fun uu___1 ->
                  (fun ps ->
                     let ps = Obj.magic ps in
                     let uu___1 = __tc e t1 in
                     Obj.magic
                       (FStarC_Class_Monad.op_let_Bang
                          FStarC_Tactics_Monad.monad_tac () ()
                          (Obj.magic uu___1)
                          (fun uu___2 ->
                             (fun uu___2 ->
                                let uu___2 = Obj.magic uu___2 in
                                match uu___2 with
                                | (t11, ty1, g1) ->
                                    let uu___3 = __tc e t2 in
                                    Obj.magic
                                      (FStarC_Class_Monad.op_let_Bang
                                         FStarC_Tactics_Monad.monad_tac () ()
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
                                                       ps.FStarC_Tactics_Types.entry_range in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_let_Bang
                                                        FStarC_Tactics_Monad.monad_tac
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
                                                                  ps.FStarC_Tactics_Types.entry_range in
                                                              Obj.magic
                                                                (FStarC_Class_Monad.op_let_Bang
                                                                   FStarC_Tactics_Monad.monad_tac
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
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    (Obj.repr
                                                                    (ret
                                                                    false))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g11 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    do_unify_maybe_guards
                                                                    true
                                                                    must_tot
                                                                    e t11 t21 in
                                                                    FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    (Obj.repr
                                                                    (ret
                                                                    false))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g21 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let formula
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    guard_formula
                                                                    g11 in
                                                                    let uu___14
                                                                    =
                                                                    guard_formula
                                                                    g21 in
                                                                    FStarC_Syntax_Util.mk_conj
                                                                    uu___13
                                                                    uu___14 in
                                                                    let uu___13
                                                                    =
                                                                    FStarC_Tactics_Monad.goal_of_guard
                                                                    "unify_guard_env.g2"
                                                                    e formula
                                                                    FStar_Pervasives_Native.None
                                                                    ps.FStarC_Tactics_Types.entry_range in
                                                                    FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    FStarC_Tactics_Monad.push_goals
                                                                    [goal] in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    (ret true))
                                                                    uu___15)))
                                                                    uu___14))))
                                                                    uu___12))))
                                                                    uu___10)))
                                                                    uu___8)))
                                                             uu___6))) uu___4)))
                               uu___2))) uu___1)) in
        FStarC_Tactics_Monad.wrap_err "unify_guard_env" uu___
let (launch_process :
  Prims.string ->
    Prims.string Prims.list ->
      Prims.string -> Prims.string FStarC_Tactics_Monad.tac)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun prog ->
           fun args ->
             fun input ->
               Obj.magic
                 (FStarC_Class_Monad.op_let_Bang
                    FStarC_Tactics_Monad.monad_tac () () idtac
                    (fun uu___ ->
                       (fun uu___ ->
                          let uu___ = Obj.magic uu___ in
                          let uu___1 = FStarC_Options.unsafe_tactic_exec () in
                          if uu___1
                          then
                            let s =
                              FStarC_Compiler_Util.run_process
                                "tactic_launch" prog args
                                (FStar_Pervasives_Native.Some input) in
                            Obj.magic (ret s)
                          else
                            Obj.magic
                              (FStarC_Tactics_Monad.fail
                                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided"))
                         uu___))) uu___2 uu___1 uu___
let (fresh_bv_named :
  Prims.string -> FStarC_Syntax_Syntax.bv FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    (fun nm ->
       Obj.magic
         (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
            idtac
            (fun uu___ ->
               (fun uu___ ->
                  let uu___ = Obj.magic uu___ in
                  let uu___1 =
                    FStarC_Syntax_Syntax.gen_bv nm
                      FStar_Pervasives_Native.None FStarC_Syntax_Syntax.tun in
                  Obj.magic (ret uu___1)) uu___))) uu___
let (change : FStarC_Syntax_Syntax.typ -> unit FStarC_Tactics_Monad.tac) =
  fun ty ->
    let uu___ =
      let uu___1 =
        FStarC_Tactics_Monad.if_verbose
          (fun uu___2 ->
             let uu___3 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term ty in
             FStarC_Compiler_Util.print1 "change: ty = %s\n" uu___3) in
      FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
        uu___1
        (fun uu___2 ->
           (fun uu___2 ->
              let uu___2 = Obj.magic uu___2 in
              Obj.magic
                (FStarC_Class_Monad.op_let_Bang
                   FStarC_Tactics_Monad.monad_tac () ()
                   (Obj.magic FStarC_Tactics_Monad.cur_goal)
                   (fun uu___3 ->
                      (fun g ->
                         let g = Obj.magic g in
                         let uu___3 =
                           let uu___4 = FStarC_Tactics_Types.goal_env g in
                           __tc uu___4 ty in
                         Obj.magic
                           (FStarC_Class_Monad.op_let_Bang
                              FStarC_Tactics_Monad.monad_tac () ()
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun uu___4 ->
                                    let uu___4 = Obj.magic uu___4 in
                                    match uu___4 with
                                    | (ty1, uu___5, guard) ->
                                        let uu___6 =
                                          let uu___7 =
                                            FStarC_Tactics_Types.goal_env g in
                                          let uu___8 =
                                            let uu___9 =
                                              should_check_goal_uvar g in
                                            FStar_Pervasives_Native.Some
                                              uu___9 in
                                          proc_guard "change" uu___7 guard
                                            uu___8 (rangeof g) in
                                        Obj.magic
                                          (FStarC_Class_Monad.op_let_Bang
                                             FStarC_Tactics_Monad.monad_tac
                                             () () uu___6
                                             (fun uu___7 ->
                                                (fun uu___7 ->
                                                   let uu___7 =
                                                     Obj.magic uu___7 in
                                                   let must_tot = true in
                                                   let uu___8 =
                                                     let uu___9 =
                                                       FStarC_Tactics_Types.goal_env
                                                         g in
                                                     let uu___10 =
                                                       FStarC_Tactics_Types.goal_type
                                                         g in
                                                     do_unify must_tot uu___9
                                                       uu___10 ty1 in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_let_Bang
                                                        FStarC_Tactics_Monad.monad_tac
                                                        () ()
                                                        (Obj.magic uu___8)
                                                        (fun uu___9 ->
                                                           (fun bb ->
                                                              let bb =
                                                                Obj.magic bb in
                                                              if bb
                                                              then
                                                                let uu___9 =
                                                                  goal_with_type
                                                                    g ty1 in
                                                                Obj.magic
                                                                  (FStarC_Tactics_Monad.replace_cur
                                                                    uu___9)
                                                              else
                                                                (let steps =
                                                                   [FStarC_TypeChecker_Env.AllowUnboundUniverses;
                                                                   FStarC_TypeChecker_Env.UnfoldUntil
                                                                    FStarC_Syntax_Syntax.delta_constant;
                                                                   FStarC_TypeChecker_Env.Primops] in
                                                                 let ng =
                                                                   let uu___10
                                                                    =
                                                                    FStarC_Tactics_Types.goal_env
                                                                    g in
                                                                   let uu___11
                                                                    =
                                                                    FStarC_Tactics_Types.goal_type
                                                                    g in
                                                                   normalize
                                                                    steps
                                                                    uu___10
                                                                    uu___11 in
                                                                 let nty =
                                                                   let uu___10
                                                                    =
                                                                    FStarC_Tactics_Types.goal_env
                                                                    g in
                                                                   normalize
                                                                    steps
                                                                    uu___10
                                                                    ty1 in
                                                                 let uu___10
                                                                   =
                                                                   let uu___11
                                                                    =
                                                                    FStarC_Tactics_Types.goal_env
                                                                    g in
                                                                   do_unify
                                                                    must_tot
                                                                    uu___11
                                                                    ng nty in
                                                                 Obj.magic
                                                                   (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    goal_with_type
                                                                    g ty1 in
                                                                    Obj.magic
                                                                    (FStarC_Tactics_Monad.replace_cur
                                                                    uu___11)
                                                                    else
                                                                    Obj.magic
                                                                    (FStarC_Tactics_Monad.fail
                                                                    "not convertible"))
                                                                    uu___11))))
                                                             uu___9))) uu___7)))
                                   uu___4))) uu___3))) uu___2) in
    FStarC_Tactics_Monad.wrap_err "change" uu___
let (failwhen : Prims.bool -> Prims.string -> unit FStarC_Tactics_Monad.tac)
  = fun b -> fun msg -> if b then FStarC_Tactics_Monad.fail msg else ret ()
let (t_destruct :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.fv * FStarC_BigInt.t) Prims.list
      FStarC_Tactics_Monad.tac)
  =
  fun s_tm ->
    let uu___ =
      Obj.magic
        (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
           (Obj.magic FStarC_Tactics_Monad.cur_goal)
           (fun uu___1 ->
              (fun g ->
                 let g = Obj.magic g in
                 let uu___1 =
                   let uu___2 = FStarC_Tactics_Types.goal_env g in
                   __tc uu___2 s_tm in
                 Obj.magic
                   (FStarC_Class_Monad.op_let_Bang
                      FStarC_Tactics_Monad.monad_tac () () (Obj.magic uu___1)
                      (fun uu___2 ->
                         (fun uu___2 ->
                            let uu___2 = Obj.magic uu___2 in
                            match uu___2 with
                            | (s_tm1, s_ty, guard) ->
                                let uu___3 =
                                  let uu___4 =
                                    FStarC_Tactics_Types.goal_env g in
                                  let uu___5 =
                                    let uu___6 = should_check_goal_uvar g in
                                    FStar_Pervasives_Native.Some uu___6 in
                                  proc_guard "destruct" uu___4 guard uu___5
                                    (rangeof g) in
                                Obj.magic
                                  (FStarC_Class_Monad.op_let_Bang
                                     FStarC_Tactics_Monad.monad_tac () ()
                                     uu___3
                                     (fun uu___4 ->
                                        (fun uu___4 ->
                                           let uu___4 = Obj.magic uu___4 in
                                           let s_ty1 =
                                             let uu___5 =
                                               FStarC_Tactics_Types.goal_env
                                                 g in
                                             FStarC_TypeChecker_Normalize.normalize
                                               [FStarC_TypeChecker_Env.DontUnfoldAttr
                                                  [FStarC_Parser_Const.tac_opaque_attr];
                                               FStarC_TypeChecker_Env.Weak;
                                               FStarC_TypeChecker_Env.HNF;
                                               FStarC_TypeChecker_Env.UnfoldUntil
                                                 FStarC_Syntax_Syntax.delta_constant]
                                               uu___5 s_ty in
                                           let uu___5 =
                                             let uu___6 =
                                               FStarC_Syntax_Util.unrefine
                                                 s_ty1 in
                                             FStarC_Syntax_Util.head_and_args_full
                                               uu___6 in
                                           match uu___5 with
                                           | (h, args) ->
                                               let uu___6 =
                                                 let uu___7 =
                                                   let uu___8 =
                                                     FStarC_Syntax_Subst.compress
                                                       h in
                                                   uu___8.FStarC_Syntax_Syntax.n in
                                                 match uu___7 with
                                                 | FStarC_Syntax_Syntax.Tm_fvar
                                                     fv -> ret (fv, [])
                                                 | FStarC_Syntax_Syntax.Tm_uinst
                                                     (h', us) ->
                                                     let uu___8 =
                                                       let uu___9 =
                                                         FStarC_Syntax_Subst.compress
                                                           h' in
                                                       uu___9.FStarC_Syntax_Syntax.n in
                                                     (match uu___8 with
                                                      | FStarC_Syntax_Syntax.Tm_fvar
                                                          fv -> ret (fv, us)
                                                      | uu___9 ->
                                                          failwith
                                                            "impossible: uinst over something that's not an fvar")
                                                 | uu___8 ->
                                                     FStarC_Tactics_Monad.fail
                                                       "type is not an fv" in
                                               Obj.magic
                                                 (FStarC_Class_Monad.op_let_Bang
                                                    FStarC_Tactics_Monad.monad_tac
                                                    () () (Obj.magic uu___6)
                                                    (fun uu___7 ->
                                                       (fun uu___7 ->
                                                          let uu___7 =
                                                            Obj.magic uu___7 in
                                                          match uu___7 with
                                                          | (fv, a_us) ->
                                                              let t_lid =
                                                                FStarC_Syntax_Syntax.lid_of_fv
                                                                  fv in
                                                              let uu___8 =
                                                                let uu___9 =
                                                                  FStarC_Tactics_Types.goal_env
                                                                    g in
                                                                FStarC_TypeChecker_Env.lookup_sigelt
                                                                  uu___9
                                                                  t_lid in
                                                              (match uu___8
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                   ->
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStarC_Tactics_Monad.fail
                                                                    "type not found in environment"))
                                                               | FStar_Pervasives_Native.Some
                                                                   se ->
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    se.FStarC_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Sig_inductive_typ
                                                                    {
                                                                    FStarC_Syntax_Syntax.lid
                                                                    = uu___9;
                                                                    FStarC_Syntax_Syntax.us
                                                                    = t_us;
                                                                    FStarC_Syntax_Syntax.params
                                                                    = t_ps;
                                                                    FStarC_Syntax_Syntax.num_uniform_params
                                                                    = uu___10;
                                                                    FStarC_Syntax_Syntax.t
                                                                    = t_ty;
                                                                    FStarC_Syntax_Syntax.mutuals
                                                                    = mut;
                                                                    FStarC_Syntax_Syntax.ds
                                                                    = c_lids;
                                                                    FStarC_Syntax_Syntax.injective_type_params
                                                                    = uu___11;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let erasable
                                                                    =
                                                                    FStarC_Syntax_Util.has_attribute
                                                                    se.FStarC_Syntax_Syntax.sigattrs
                                                                    FStarC_Parser_Const.erasable_attr in
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    erasable
                                                                    &&
                                                                    (let uu___14
                                                                    =
                                                                    is_irrelevant
                                                                    g in
                                                                    Prims.op_Negation
                                                                    uu___14) in
                                                                    failwhen
                                                                    uu___13
                                                                    "cannot destruct erasable type to solve proof-relevant goal" in
                                                                    FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___12
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    uu___13 in
                                                                    let uu___14
                                                                    =
                                                                    failwhen
                                                                    ((FStarC_Compiler_List.length
                                                                    a_us) <>
                                                                    (FStarC_Compiler_List.length
                                                                    t_us))
                                                                    "t_us don't match?" in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    let uu___16
                                                                    =
                                                                    FStarC_Syntax_Subst.open_term
                                                                    t_ps t_ty in
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    (t_ps1,
                                                                    t_ty1) ->
                                                                    let uu___17
                                                                    =
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.mapM
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    c_lid ->
                                                                    let c_lid
                                                                    =
                                                                    Obj.magic
                                                                    c_lid in
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Tactics_Types.goal_env
                                                                    g in
                                                                    FStarC_TypeChecker_Env.lookup_sigelt
                                                                    uu___19
                                                                    c_lid in
                                                                    match uu___18
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStarC_Tactics_Monad.fail
                                                                    "ctor not found?"))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    se1.FStarC_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Sig_datacon
                                                                    {
                                                                    FStarC_Syntax_Syntax.lid1
                                                                    = uu___19;
                                                                    FStarC_Syntax_Syntax.us1
                                                                    = c_us;
                                                                    FStarC_Syntax_Syntax.t1
                                                                    = c_ty;
                                                                    FStarC_Syntax_Syntax.ty_lid
                                                                    = uu___20;
                                                                    FStarC_Syntax_Syntax.num_ty_params
                                                                    = nparam;
                                                                    FStarC_Syntax_Syntax.mutuals1
                                                                    = mut1;
                                                                    FStarC_Syntax_Syntax.injective_type_params1
                                                                    = uu___21;_}
                                                                    ->
                                                                    Obj.repr
                                                                    (let fv1
                                                                    =
                                                                    FStarC_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    (FStar_Pervasives_Native.Some
                                                                    FStarC_Syntax_Syntax.Data_ctor) in
                                                                    let uu___22
                                                                    =
                                                                    failwhen
                                                                    ((FStarC_Compiler_List.length
                                                                    a_us) <>
                                                                    (FStarC_Compiler_List.length
                                                                    c_us))
                                                                    "t_us don't match?" in
                                                                    FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___22
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    Obj.magic
                                                                    uu___23 in
                                                                    let s =
                                                                    FStarC_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us in
                                                                    let c_ty1
                                                                    =
                                                                    FStarC_Syntax_Subst.subst
                                                                    s c_ty in
                                                                    let uu___24
                                                                    =
                                                                    FStarC_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1) in
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    (c_us1,
                                                                    c_ty2) ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_Syntax_Util.arrow_formals_comp
                                                                    c_ty2 in
                                                                    (match uu___25
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    comp) ->
                                                                    let uu___26
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStarC_Syntax_Syntax.ppname in
                                                                    let ppname1
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Ident.showable_ident
                                                                    ppname in
                                                                    Prims.strcat
                                                                    "a"
                                                                    uu___29 in
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Ident.range_of_id
                                                                    ppname in
                                                                    (uu___28,
                                                                    uu___29) in
                                                                    FStarC_Ident.mk_ident
                                                                    uu___27 in
                                                                    FStarC_Syntax_Syntax.freshen_bv
                                                                    {
                                                                    FStarC_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStarC_Syntax_Syntax.index
                                                                    =
                                                                    (bv.FStarC_Syntax_Syntax.index);
                                                                    FStarC_Syntax_Syntax.sort
                                                                    =
                                                                    (bv.FStarC_Syntax_Syntax.sort)
                                                                    } in
                                                                    let bs' =
                                                                    FStarC_Compiler_List.map
                                                                    (fun b ->
                                                                    let uu___27
                                                                    =
                                                                    rename_bv
                                                                    b.FStarC_Syntax_Syntax.binder_bv in
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = uu___27;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    =
                                                                    (b.FStarC_Syntax_Syntax.binder_qual);
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    =
                                                                    (b.FStarC_Syntax_Syntax.binder_positivity);
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    =
                                                                    (b.FStarC_Syntax_Syntax.binder_attrs)
                                                                    }) bs in
                                                                    let subst
                                                                    =
                                                                    FStarC_Compiler_List.map2
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    fun
                                                                    uu___28
                                                                    ->
                                                                    match 
                                                                    (uu___27,
                                                                    uu___28)
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___29;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___30;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___31;_},
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = bv';
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___32;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___33;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___34;_})
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    bv' in
                                                                    (bv,
                                                                    uu___36) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___35)
                                                                    bs bs' in
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Syntax_Subst.subst_binders
                                                                    subst bs' in
                                                                    let uu___28
                                                                    =
                                                                    FStarC_Syntax_Subst.subst_comp
                                                                    subst
                                                                    comp in
                                                                    (uu___27,
                                                                    uu___28) in
                                                                    (match uu___26
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    comp1) ->
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Compiler_List.splitAt
                                                                    nparam
                                                                    bs1 in
                                                                    (match uu___27
                                                                    with
                                                                    | 
                                                                    (d_ps,
                                                                    bs2) ->
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStarC_Syntax_Util.is_total_comp
                                                                    comp1 in
                                                                    Prims.op_Negation
                                                                    uu___30 in
                                                                    failwhen
                                                                    uu___29
                                                                    "not total?" in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___28
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    Obj.magic
                                                                    uu___29 in
                                                                    let mk_pat
                                                                    p =
                                                                    {
                                                                    FStarC_Syntax_Syntax.v
                                                                    = p;
                                                                    FStarC_Syntax_Syntax.p
                                                                    =
                                                                    (s_tm1.FStarC_Syntax_Syntax.pos)
                                                                    } in
                                                                    let is_imp
                                                                    uu___30 =
                                                                    match uu___30
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStarC_Syntax_Syntax.Implicit
                                                                    uu___31)
                                                                    -> true
                                                                    | 
                                                                    uu___31
                                                                    -> false in
                                                                    let uu___30
                                                                    =
                                                                    FStarC_Compiler_List.splitAt
                                                                    nparam
                                                                    args in
                                                                    match uu___30
                                                                    with
                                                                    | 
                                                                    (a_ps,
                                                                    a_is) ->
                                                                    let uu___31
                                                                    =
                                                                    failwhen
                                                                    ((FStarC_Compiler_List.length
                                                                    a_ps) <>
                                                                    (FStarC_Compiler_List.length
                                                                    d_ps))
                                                                    "params not match?" in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___31
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    Obj.magic
                                                                    uu___32 in
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStarC_Compiler_List.zip
                                                                    d_ps a_ps in
                                                                    let subst
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    match uu___33
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___34;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___35;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___36;_},
                                                                    (t,
                                                                    uu___37))
                                                                    ->
                                                                    FStarC_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps in
                                                                    let bs3 =
                                                                    FStarC_Syntax_Subst.subst_binders
                                                                    subst bs2 in
                                                                    let subpats_1
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    match uu___33
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___34;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___35;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___36;_},
                                                                    (t,
                                                                    uu___37))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStarC_Syntax_Syntax.Pat_dot_term
                                                                    (FStar_Pervasives_Native.Some
                                                                    t))),
                                                                    true))
                                                                    d_ps_a_ps in
                                                                    let subpats_2
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    match uu___33
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = bq;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___34;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___35;_}
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStarC_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    bq))) bs3 in
                                                                    let subpats
                                                                    =
                                                                    FStarC_Compiler_List.op_At
                                                                    subpats_1
                                                                    subpats_2 in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStarC_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    a_us),
                                                                    subpats)) in
                                                                    let env1
                                                                    =
                                                                    FStarC_Tactics_Types.goal_env
                                                                    g in
                                                                    let cod =
                                                                    FStarC_Tactics_Types.goal_type
                                                                    g in
                                                                    let equ =
                                                                    env1.FStarC_TypeChecker_Env.universe_of
                                                                    env1
                                                                    s_ty1 in
                                                                    let uu___33
                                                                    =
                                                                    FStarC_TypeChecker_TcTerm.tc_pat
                                                                    {
                                                                    FStarC_TypeChecker_Env.solver
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.solver);
                                                                    FStarC_TypeChecker_Env.range
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.range);
                                                                    FStarC_TypeChecker_Env.curmodule
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.curmodule);
                                                                    FStarC_TypeChecker_Env.gamma
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.gamma);
                                                                    FStarC_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.gamma_sig);
                                                                    FStarC_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.gamma_cache);
                                                                    FStarC_TypeChecker_Env.modules
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.modules);
                                                                    FStarC_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.expected_typ);
                                                                    FStarC_TypeChecker_Env.sigtab
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.sigtab);
                                                                    FStarC_TypeChecker_Env.attrtab
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.attrtab);
                                                                    FStarC_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.instantiate_imp);
                                                                    FStarC_TypeChecker_Env.effects
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.effects);
                                                                    FStarC_TypeChecker_Env.generalize
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.generalize);
                                                                    FStarC_TypeChecker_Env.letrecs
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.letrecs);
                                                                    FStarC_TypeChecker_Env.top_level
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.top_level);
                                                                    FStarC_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.check_uvars);
                                                                    FStarC_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.use_eq_strict);
                                                                    FStarC_TypeChecker_Env.is_iface
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.is_iface);
                                                                    FStarC_TypeChecker_Env.admit
                                                                    = true;
                                                                    FStarC_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.lax_universes);
                                                                    FStarC_TypeChecker_Env.phase1
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.phase1);
                                                                    FStarC_TypeChecker_Env.failhard
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.failhard);
                                                                    FStarC_TypeChecker_Env.flychecking
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.flychecking);
                                                                    FStarC_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                                                                    FStarC_TypeChecker_Env.intactics
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.intactics);
                                                                    FStarC_TypeChecker_Env.nocoerce
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.nocoerce);
                                                                    FStarC_TypeChecker_Env.tc_term
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.tc_term);
                                                                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                                                    FStarC_TypeChecker_Env.universe_of
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.universe_of);
                                                                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                                                    FStarC_TypeChecker_Env.teq_nosmt_force
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                                                                    FStarC_TypeChecker_Env.subtype_nosmt_force
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                                                    FStarC_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStarC_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                                                                    FStarC_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                                                                    FStarC_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.proof_ns);
                                                                    FStarC_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.synth_hook);
                                                                    FStarC_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStarC_TypeChecker_Env.splice
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.splice);
                                                                    FStarC_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.mpreprocess);
                                                                    FStarC_TypeChecker_Env.postprocess
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.postprocess);
                                                                    FStarC_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.identifier_info);
                                                                    FStarC_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.tc_hooks);
                                                                    FStarC_TypeChecker_Env.dsenv
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.dsenv);
                                                                    FStarC_TypeChecker_Env.nbe
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.nbe);
                                                                    FStarC_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.strict_args_tab);
                                                                    FStarC_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                                                                    FStarC_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                                                    FStarC_TypeChecker_Env.unif_allow_ref_guards
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                                                    FStarC_TypeChecker_Env.erase_erasable_args
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                                                                    FStarC_TypeChecker_Env.core_check
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.core_check);
                                                                    FStarC_TypeChecker_Env.missing_decl
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.missing_decl)
                                                                    } s_ty1
                                                                    pat in
                                                                    match uu___33
                                                                    with
                                                                    | 
                                                                    (uu___34,
                                                                    uu___35,
                                                                    uu___36,
                                                                    uu___37,
                                                                    pat_t,
                                                                    uu___38,
                                                                    _guard_pat,
                                                                    _erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    FStarC_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t in
                                                                    FStarC_Syntax_Util.mk_squash
                                                                    FStarC_Syntax_Syntax.U_zero
                                                                    uu___40 in
                                                                    FStarC_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu___39 in
                                                                    let cod1
                                                                    =
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_binder
                                                                    eq_b in
                                                                    [uu___40] in
                                                                    let uu___40
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_Total
                                                                    cod in
                                                                    FStarC_Syntax_Util.arrow
                                                                    uu___39
                                                                    uu___40 in
                                                                    let nty =
                                                                    let uu___39
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_Total
                                                                    cod1 in
                                                                    FStarC_Syntax_Util.arrow
                                                                    bs3
                                                                    uu___39 in
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    goal_typedness_deps
                                                                    g in
                                                                    FStarC_Tactics_Monad.new_uvar
                                                                    "destruct branch"
                                                                    env1 nty
                                                                    FStar_Pervasives_Native.None
                                                                    uu___40
                                                                    (rangeof
                                                                    g) in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___39)
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    let uu___40
                                                                    =
                                                                    Obj.magic
                                                                    uu___40 in
                                                                    match uu___40
                                                                    with
                                                                    | 
                                                                    (uvt, uv)
                                                                    ->
                                                                    let g' =
                                                                    FStarC_Tactics_Types.mk_goal
                                                                    env1 uv
                                                                    g.FStarC_Tactics_Types.opts
                                                                    false
                                                                    g.FStarC_Tactics_Types.label in
                                                                    let brt =
                                                                    FStarC_Syntax_Util.mk_app_binders
                                                                    uvt bs3 in
                                                                    let brt1
                                                                    =
                                                                    let uu___41
                                                                    =
                                                                    let uu___42
                                                                    =
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    FStarC_Syntax_Util.exp_unit in
                                                                    [uu___42] in
                                                                    FStarC_Syntax_Util.mk_app
                                                                    brt
                                                                    uu___41 in
                                                                    let br =
                                                                    FStarC_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1) in
                                                                    let uu___41
                                                                    =
                                                                    let uu___42
                                                                    =
                                                                    let uu___43
                                                                    =
                                                                    FStarC_BigInt.of_int_fs
                                                                    (FStarC_Compiler_List.length
                                                                    bs3) in
                                                                    (fv1,
                                                                    uu___43) in
                                                                    (g', br,
                                                                    uu___42) in
                                                                    Obj.magic
                                                                    (ret
                                                                    uu___41))
                                                                    uu___40)))
                                                                    uu___32)))
                                                                    uu___29))))))
                                                                    uu___23))
                                                                    | 
                                                                    uu___19
                                                                    ->
                                                                    Obj.repr
                                                                    (FStarC_Tactics_Monad.fail
                                                                    "impossible: not a ctor"))))
                                                                    uu___18)
                                                                    (Obj.magic
                                                                    c_lids)) in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    goal_brs
                                                                    ->
                                                                    let goal_brs
                                                                    =
                                                                    Obj.magic
                                                                    goal_brs in
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Compiler_List.unzip3
                                                                    goal_brs in
                                                                    match uu___18
                                                                    with
                                                                    | 
                                                                    (goals,
                                                                    brs,
                                                                    infos) ->
                                                                    let w =
                                                                    FStarC_Syntax_Syntax.mk
                                                                    (FStarC_Syntax_Syntax.Tm_match
                                                                    {
                                                                    FStarC_Syntax_Syntax.scrutinee
                                                                    = s_tm1;
                                                                    FStarC_Syntax_Syntax.ret_opt
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    FStarC_Syntax_Syntax.brs
                                                                    = brs;
                                                                    FStarC_Syntax_Syntax.rc_opt1
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })
                                                                    s_tm1.FStarC_Syntax_Syntax.pos in
                                                                    let uu___19
                                                                    =
                                                                    solve' g
                                                                    w in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
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
                                                                    mark_goal_implicit_already_checked
                                                                    g;
                                                                    (
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Tactics_Monad.add_goals
                                                                    goals in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Tactics_Monad.monad_tac
                                                                    () ()
                                                                    uu___22
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    Obj.magic
                                                                    uu___23 in
                                                                    Obj.magic
                                                                    (ret
                                                                    infos))
                                                                    uu___23))))
                                                                    uu___20)))
                                                                    uu___18)))
                                                                    uu___15)))
                                                                    uu___13))
                                                                    | 
                                                                    uu___9 ->
                                                                    Obj.repr
                                                                    (FStarC_Tactics_Monad.fail
                                                                    "not an inductive type")))))
                                                         uu___7))) uu___4)))
                           uu___2))) uu___1)) in
    FStarC_Tactics_Monad.wrap_err "destruct" uu___
let (gather_explicit_guards_for_resolved_goals :
  unit -> unit FStarC_Tactics_Monad.tac) = fun uu___ -> ret ()
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu___::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu___ = init xs in x :: uu___
let rec (inspect :
  FStarC_Syntax_Syntax.term ->
    FStarC_Reflection_V1_Data.term_view FStarC_Tactics_Monad.tac)
  =
  fun t ->
    let uu___ =
      let uu___1 = top_env () in
      Obj.magic
        (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
           (Obj.magic uu___1)
           (fun uu___2 ->
              (fun e ->
                 let e = Obj.magic e in
                 let t1 = FStarC_Syntax_Util.unlazy_emb t in
                 let t2 = FStarC_Syntax_Subst.compress t1 in
                 match t2.FStarC_Syntax_Syntax.n with
                 | FStarC_Syntax_Syntax.Tm_meta
                     { FStarC_Syntax_Syntax.tm2 = t3;
                       FStarC_Syntax_Syntax.meta = uu___2;_}
                     -> Obj.magic (inspect t3)
                 | FStarC_Syntax_Syntax.Tm_name bv ->
                     Obj.magic (ret (FStarC_Reflection_V1_Data.Tv_Var bv))
                 | FStarC_Syntax_Syntax.Tm_bvar bv ->
                     Obj.magic (ret (FStarC_Reflection_V1_Data.Tv_BVar bv))
                 | FStarC_Syntax_Syntax.Tm_fvar fv ->
                     Obj.magic (ret (FStarC_Reflection_V1_Data.Tv_FVar fv))
                 | FStarC_Syntax_Syntax.Tm_uinst (t3, us) ->
                     let uu___2 =
                       let uu___3 =
                         let uu___4 = FStarC_Syntax_Subst.compress t3 in
                         FStarC_Syntax_Util.unascribe uu___4 in
                       uu___3.FStarC_Syntax_Syntax.n in
                     (match uu___2 with
                      | FStarC_Syntax_Syntax.Tm_fvar fv ->
                          Obj.magic
                            (ret
                               (FStarC_Reflection_V1_Data.Tv_UInst (fv, us)))
                      | uu___3 ->
                          Obj.magic
                            (failwith
                               "Tac::inspect: Tm_uinst head not an fvar"))
                 | FStarC_Syntax_Syntax.Tm_ascribed
                     { FStarC_Syntax_Syntax.tm = t3;
                       FStarC_Syntax_Syntax.asc =
                         (FStar_Pervasives.Inl ty, tacopt, eq);
                       FStarC_Syntax_Syntax.eff_opt = uu___2;_}
                     ->
                     Obj.magic
                       (ret
                          (FStarC_Reflection_V1_Data.Tv_AscribedT
                             (t3, ty, tacopt, eq)))
                 | FStarC_Syntax_Syntax.Tm_ascribed
                     { FStarC_Syntax_Syntax.tm = t3;
                       FStarC_Syntax_Syntax.asc =
                         (FStar_Pervasives.Inr cty, tacopt, eq);
                       FStarC_Syntax_Syntax.eff_opt = uu___2;_}
                     ->
                     Obj.magic
                       (ret
                          (FStarC_Reflection_V1_Data.Tv_AscribedC
                             (t3, cty, tacopt, eq)))
                 | FStarC_Syntax_Syntax.Tm_app
                     { FStarC_Syntax_Syntax.hd = uu___2;
                       FStarC_Syntax_Syntax.args = [];_}
                     -> Obj.magic (failwith "empty arguments on Tm_app")
                 | FStarC_Syntax_Syntax.Tm_app
                     { FStarC_Syntax_Syntax.hd = hd;
                       FStarC_Syntax_Syntax.args = args;_}
                     ->
                     let uu___2 = last args in
                     (match uu___2 with
                      | (a, q) ->
                          let q' =
                            FStarC_Reflection_V1_Builtins.inspect_aqual q in
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                let uu___6 = init args in
                                FStarC_Syntax_Syntax.mk_Tm_app hd uu___6
                                  t2.FStarC_Syntax_Syntax.pos in
                              (uu___5, (a, q')) in
                            FStarC_Reflection_V1_Data.Tv_App uu___4 in
                          Obj.magic (ret uu___3))
                 | FStarC_Syntax_Syntax.Tm_abs
                     { FStarC_Syntax_Syntax.bs = [];
                       FStarC_Syntax_Syntax.body = uu___2;
                       FStarC_Syntax_Syntax.rc_opt = uu___3;_}
                     -> Obj.magic (failwith "empty arguments on Tm_abs")
                 | FStarC_Syntax_Syntax.Tm_abs
                     { FStarC_Syntax_Syntax.bs = bs;
                       FStarC_Syntax_Syntax.body = t3;
                       FStarC_Syntax_Syntax.rc_opt = k;_}
                     ->
                     let uu___2 = FStarC_Syntax_Subst.open_term bs t3 in
                     (match uu___2 with
                      | (bs1, t4) ->
                          (match bs1 with
                           | [] -> Obj.magic (failwith "impossible")
                           | b::bs2 ->
                               let uu___3 =
                                 let uu___4 =
                                   let uu___5 =
                                     FStarC_Syntax_Util.abs bs2 t4 k in
                                   (b, uu___5) in
                                 FStarC_Reflection_V1_Data.Tv_Abs uu___4 in
                               Obj.magic (ret uu___3)))
                 | FStarC_Syntax_Syntax.Tm_type u ->
                     Obj.magic (ret (FStarC_Reflection_V1_Data.Tv_Type u))
                 | FStarC_Syntax_Syntax.Tm_arrow
                     { FStarC_Syntax_Syntax.bs1 = [];
                       FStarC_Syntax_Syntax.comp = uu___2;_}
                     -> Obj.magic (failwith "empty binders on arrow")
                 | FStarC_Syntax_Syntax.Tm_arrow uu___2 ->
                     let uu___3 = FStarC_Syntax_Util.arrow_one t2 in
                     (match uu___3 with
                      | FStar_Pervasives_Native.Some (b, c) ->
                          Obj.magic
                            (ret (FStarC_Reflection_V1_Data.Tv_Arrow (b, c)))
                      | FStar_Pervasives_Native.None ->
                          Obj.magic (failwith "impossible"))
                 | FStarC_Syntax_Syntax.Tm_refine
                     { FStarC_Syntax_Syntax.b = bv;
                       FStarC_Syntax_Syntax.phi = t3;_}
                     ->
                     let b = FStarC_Syntax_Syntax.mk_binder bv in
                     let uu___2 = FStarC_Syntax_Subst.open_term [b] t3 in
                     (match uu___2 with
                      | (b', t4) ->
                          let b1 =
                            match b' with
                            | b'1::[] -> b'1
                            | uu___3 -> failwith "impossible" in
                          Obj.magic
                            (ret
                               (FStarC_Reflection_V1_Data.Tv_Refine
                                  ((b1.FStarC_Syntax_Syntax.binder_bv),
                                    ((b1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort),
                                    t4))))
                 | FStarC_Syntax_Syntax.Tm_constant c ->
                     let uu___2 =
                       let uu___3 =
                         FStarC_Reflection_V1_Builtins.inspect_const c in
                       FStarC_Reflection_V1_Data.Tv_Const uu___3 in
                     Obj.magic (ret uu___2)
                 | FStarC_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
                     let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             FStarC_Syntax_Unionfind.uvar_unique_id
                               ctx_u.FStarC_Syntax_Syntax.ctx_uvar_head in
                           FStarC_BigInt.of_int_fs uu___5 in
                         (uu___4, (ctx_u, s)) in
                       FStarC_Reflection_V1_Data.Tv_Uvar uu___3 in
                     Obj.magic (ret uu___2)
                 | FStarC_Syntax_Syntax.Tm_let
                     { FStarC_Syntax_Syntax.lbs = (false, lb::[]);
                       FStarC_Syntax_Syntax.body1 = t21;_}
                     ->
                     if lb.FStarC_Syntax_Syntax.lbunivs <> []
                     then Obj.magic (ret FStarC_Reflection_V1_Data.Tv_Unsupp)
                     else
                       (match lb.FStarC_Syntax_Syntax.lbname with
                        | FStar_Pervasives.Inr uu___3 ->
                            Obj.magic
                              (ret FStarC_Reflection_V1_Data.Tv_Unsupp)
                        | FStar_Pervasives.Inl bv ->
                            let b = FStarC_Syntax_Syntax.mk_binder bv in
                            let uu___3 =
                              FStarC_Syntax_Subst.open_term [b] t21 in
                            (match uu___3 with
                             | (bs, t22) ->
                                 let b1 =
                                   match bs with
                                   | b2::[] -> b2
                                   | uu___4 ->
                                       failwith
                                         "impossible: open_term returned different amount of binders" in
                                 Obj.magic
                                   (ret
                                      (FStarC_Reflection_V1_Data.Tv_Let
                                         (false,
                                           (lb.FStarC_Syntax_Syntax.lbattrs),
                                           (b1.FStarC_Syntax_Syntax.binder_bv),
                                           (bv.FStarC_Syntax_Syntax.sort),
                                           (lb.FStarC_Syntax_Syntax.lbdef),
                                           t22)))))
                 | FStarC_Syntax_Syntax.Tm_let
                     { FStarC_Syntax_Syntax.lbs = (true, lb::[]);
                       FStarC_Syntax_Syntax.body1 = t21;_}
                     ->
                     if lb.FStarC_Syntax_Syntax.lbunivs <> []
                     then Obj.magic (ret FStarC_Reflection_V1_Data.Tv_Unsupp)
                     else
                       (match lb.FStarC_Syntax_Syntax.lbname with
                        | FStar_Pervasives.Inr uu___3 ->
                            Obj.magic
                              (ret FStarC_Reflection_V1_Data.Tv_Unsupp)
                        | FStar_Pervasives.Inl bv ->
                            let uu___3 =
                              FStarC_Syntax_Subst.open_let_rec [lb] t21 in
                            (match uu___3 with
                             | (lbs, t22) ->
                                 (match lbs with
                                  | lb1::[] ->
                                      (match lb1.FStarC_Syntax_Syntax.lbname
                                       with
                                       | FStar_Pervasives.Inr uu___4 ->
                                           Obj.magic
                                             (ret
                                                FStarC_Reflection_V1_Data.Tv_Unsupp)
                                       | FStar_Pervasives.Inl bv1 ->
                                           Obj.magic
                                             (ret
                                                (FStarC_Reflection_V1_Data.Tv_Let
                                                   (true,
                                                     (lb1.FStarC_Syntax_Syntax.lbattrs),
                                                     bv1,
                                                     (bv1.FStarC_Syntax_Syntax.sort),
                                                     (lb1.FStarC_Syntax_Syntax.lbdef),
                                                     t22))))
                                  | uu___4 ->
                                      Obj.magic
                                        (failwith
                                           "impossible: open_term returned different amount of binders"))))
                 | FStarC_Syntax_Syntax.Tm_match
                     { FStarC_Syntax_Syntax.scrutinee = t3;
                       FStarC_Syntax_Syntax.ret_opt = ret_opt;
                       FStarC_Syntax_Syntax.brs = brs;
                       FStarC_Syntax_Syntax.rc_opt1 = uu___2;_}
                     ->
                     let rec inspect_pat p =
                       match p.FStarC_Syntax_Syntax.v with
                       | FStarC_Syntax_Syntax.Pat_constant c ->
                           let uu___3 =
                             FStarC_Reflection_V1_Builtins.inspect_const c in
                           FStarC_Reflection_V1_Data.Pat_Constant uu___3
                       | FStarC_Syntax_Syntax.Pat_cons (fv, us_opt, ps) ->
                           let uu___3 =
                             let uu___4 =
                               FStarC_Compiler_List.map
                                 (fun uu___5 ->
                                    match uu___5 with
                                    | (p1, b) ->
                                        let uu___6 = inspect_pat p1 in
                                        (uu___6, b)) ps in
                             (fv, us_opt, uu___4) in
                           FStarC_Reflection_V1_Data.Pat_Cons uu___3
                       | FStarC_Syntax_Syntax.Pat_var bv ->
                           FStarC_Reflection_V1_Data.Pat_Var
                             (bv,
                               (FStarC_Compiler_Sealed.seal
                                  bv.FStarC_Syntax_Syntax.sort))
                       | FStarC_Syntax_Syntax.Pat_dot_term eopt ->
                           FStarC_Reflection_V1_Data.Pat_Dot_Term eopt in
                     let brs1 =
                       FStarC_Compiler_List.map
                         FStarC_Syntax_Subst.open_branch brs in
                     let brs2 =
                       FStarC_Compiler_List.map
                         (fun uu___3 ->
                            match uu___3 with
                            | (pat, uu___4, t4) ->
                                let uu___5 = inspect_pat pat in (uu___5, t4))
                         brs1 in
                     Obj.magic
                       (ret
                          (FStarC_Reflection_V1_Data.Tv_Match
                             (t3, ret_opt, brs2)))
                 | FStarC_Syntax_Syntax.Tm_unknown ->
                     Obj.magic (ret FStarC_Reflection_V1_Data.Tv_Unknown)
                 | uu___2 ->
                     ((let uu___4 =
                         let uu___5 =
                           FStarC_Class_Tagged.tag_of
                             FStarC_Syntax_Syntax.tagged_term t2 in
                         let uu___6 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term t2 in
                         FStarC_Compiler_Util.format2
                           "inspect: outside of expected syntax (%s, %s)\n"
                           uu___5 uu___6 in
                       FStarC_Errors.log_issue
                         (FStarC_Syntax_Syntax.has_range_syntax ()) t2
                         FStarC_Errors_Codes.Warning_CantInspect ()
                         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                         (Obj.magic uu___4));
                      Obj.magic (ret FStarC_Reflection_V1_Data.Tv_Unsupp)))
                uu___2)) in
    FStarC_Tactics_Monad.wrap_err "inspect" uu___
let (pack' :
  FStarC_Reflection_V1_Data.term_view ->
    Prims.bool -> FStarC_Syntax_Syntax.term FStarC_Tactics_Monad.tac)
  =
  fun tv ->
    fun leave_curried ->
      match tv with
      | FStarC_Reflection_V1_Data.Tv_Var bv ->
          let uu___ = FStarC_Syntax_Syntax.bv_to_name bv in ret uu___
      | FStarC_Reflection_V1_Data.Tv_BVar bv ->
          let uu___ = FStarC_Syntax_Syntax.bv_to_tm bv in ret uu___
      | FStarC_Reflection_V1_Data.Tv_FVar fv ->
          let uu___ = FStarC_Syntax_Syntax.fv_to_tm fv in ret uu___
      | FStarC_Reflection_V1_Data.Tv_UInst (fv, us) ->
          let uu___ =
            let uu___1 = FStarC_Syntax_Syntax.fv_to_tm fv in
            FStarC_Syntax_Syntax.mk_Tm_uinst uu___1 us in
          ret uu___
      | FStarC_Reflection_V1_Data.Tv_App (l, (r, q)) ->
          let q' = FStarC_Reflection_V1_Builtins.pack_aqual q in
          let uu___ = FStarC_Syntax_Util.mk_app l [(r, q')] in ret uu___
      | FStarC_Reflection_V1_Data.Tv_Abs (b, t) ->
          let uu___ =
            FStarC_Syntax_Util.abs [b] t FStar_Pervasives_Native.None in
          ret uu___
      | FStarC_Reflection_V1_Data.Tv_Arrow (b, c) ->
          let uu___ =
            if leave_curried
            then FStarC_Syntax_Util.arrow [b] c
            else
              (let uu___2 = FStarC_Syntax_Util.arrow [b] c in
               FStarC_Syntax_Util.canon_arrow uu___2) in
          ret uu___
      | FStarC_Reflection_V1_Data.Tv_Type u ->
          let uu___ =
            FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_type u)
              FStarC_Compiler_Range_Type.dummyRange in
          ret uu___
      | FStarC_Reflection_V1_Data.Tv_Refine (bv, sort, t) ->
          let bv1 =
            {
              FStarC_Syntax_Syntax.ppname = (bv.FStarC_Syntax_Syntax.ppname);
              FStarC_Syntax_Syntax.index = (bv.FStarC_Syntax_Syntax.index);
              FStarC_Syntax_Syntax.sort = sort
            } in
          let uu___ = FStarC_Syntax_Util.refine bv1 t in ret uu___
      | FStarC_Reflection_V1_Data.Tv_Const c ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_Reflection_V1_Builtins.pack_const c in
              FStarC_Syntax_Syntax.Tm_constant uu___2 in
            FStarC_Syntax_Syntax.mk uu___1
              FStarC_Compiler_Range_Type.dummyRange in
          ret uu___
      | FStarC_Reflection_V1_Data.Tv_Uvar (_u, ctx_u_s) ->
          let uu___ =
            FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_uvar ctx_u_s)
              FStarC_Compiler_Range_Type.dummyRange in
          ret uu___
      | FStarC_Reflection_V1_Data.Tv_Let (false, attrs, bv, ty, t1, t2) ->
          let bv1 =
            {
              FStarC_Syntax_Syntax.ppname = (bv.FStarC_Syntax_Syntax.ppname);
              FStarC_Syntax_Syntax.index = (bv.FStarC_Syntax_Syntax.index);
              FStarC_Syntax_Syntax.sort = ty
            } in
          let lb =
            FStarC_Syntax_Util.mk_letbinding (FStar_Pervasives.Inl bv1) []
              bv1.FStarC_Syntax_Syntax.sort
              FStarC_Parser_Const.effect_Tot_lid t1 attrs
              FStarC_Compiler_Range_Type.dummyRange in
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 = FStarC_Syntax_Syntax.mk_binder bv1 in
                    [uu___5] in
                  FStarC_Syntax_Subst.close uu___4 t2 in
                {
                  FStarC_Syntax_Syntax.lbs = (false, [lb]);
                  FStarC_Syntax_Syntax.body1 = uu___3
                } in
              FStarC_Syntax_Syntax.Tm_let uu___2 in
            FStarC_Syntax_Syntax.mk uu___1
              FStarC_Compiler_Range_Type.dummyRange in
          ret uu___
      | FStarC_Reflection_V1_Data.Tv_Let (true, attrs, bv, ty, t1, t2) ->
          let bv1 =
            {
              FStarC_Syntax_Syntax.ppname = (bv.FStarC_Syntax_Syntax.ppname);
              FStarC_Syntax_Syntax.index = (bv.FStarC_Syntax_Syntax.index);
              FStarC_Syntax_Syntax.sort = ty
            } in
          let lb =
            FStarC_Syntax_Util.mk_letbinding (FStar_Pervasives.Inl bv1) []
              bv1.FStarC_Syntax_Syntax.sort
              FStarC_Parser_Const.effect_Tot_lid t1 attrs
              FStarC_Compiler_Range_Type.dummyRange in
          let uu___ = FStarC_Syntax_Subst.close_let_rec [lb] t2 in
          (match uu___ with
           | (lbs, body) ->
               let uu___1 =
                 FStarC_Syntax_Syntax.mk
                   (FStarC_Syntax_Syntax.Tm_let
                      {
                        FStarC_Syntax_Syntax.lbs = (true, lbs);
                        FStarC_Syntax_Syntax.body1 = body
                      }) FStarC_Compiler_Range_Type.dummyRange in
               ret uu___1)
      | FStarC_Reflection_V1_Data.Tv_Match (t, ret_opt, brs) ->
          let wrap v =
            {
              FStarC_Syntax_Syntax.v = v;
              FStarC_Syntax_Syntax.p = FStarC_Compiler_Range_Type.dummyRange
            } in
          let rec pack_pat p =
            match p with
            | FStarC_Reflection_V1_Data.Pat_Constant c ->
                let uu___ =
                  let uu___1 = FStarC_Reflection_V1_Builtins.pack_const c in
                  FStarC_Syntax_Syntax.Pat_constant uu___1 in
                wrap uu___
            | FStarC_Reflection_V1_Data.Pat_Cons (fv, us_opt, ps) ->
                let uu___ =
                  let uu___1 =
                    let uu___2 =
                      FStarC_Compiler_List.map
                        (fun uu___3 ->
                           match uu___3 with
                           | (p1, b) ->
                               let uu___4 = pack_pat p1 in (uu___4, b)) ps in
                    (fv, us_opt, uu___2) in
                  FStarC_Syntax_Syntax.Pat_cons uu___1 in
                wrap uu___
            | FStarC_Reflection_V1_Data.Pat_Var (bv, _sort) ->
                wrap (FStarC_Syntax_Syntax.Pat_var bv)
            | FStarC_Reflection_V1_Data.Pat_Dot_Term eopt ->
                wrap (FStarC_Syntax_Syntax.Pat_dot_term eopt) in
          let brs1 =
            FStarC_Compiler_List.map
              (fun uu___ ->
                 match uu___ with
                 | (pat, t1) ->
                     let uu___1 = pack_pat pat in
                     (uu___1, FStar_Pervasives_Native.None, t1)) brs in
          let brs2 =
            FStarC_Compiler_List.map FStarC_Syntax_Subst.close_branch brs1 in
          let uu___ =
            FStarC_Syntax_Syntax.mk
              (FStarC_Syntax_Syntax.Tm_match
                 {
                   FStarC_Syntax_Syntax.scrutinee = t;
                   FStarC_Syntax_Syntax.ret_opt = ret_opt;
                   FStarC_Syntax_Syntax.brs = brs2;
                   FStarC_Syntax_Syntax.rc_opt1 =
                     FStar_Pervasives_Native.None
                 }) FStarC_Compiler_Range_Type.dummyRange in
          ret uu___
      | FStarC_Reflection_V1_Data.Tv_AscribedT (e, t, tacopt, use_eq) ->
          let uu___ =
            FStarC_Syntax_Syntax.mk
              (FStarC_Syntax_Syntax.Tm_ascribed
                 {
                   FStarC_Syntax_Syntax.tm = e;
                   FStarC_Syntax_Syntax.asc =
                     ((FStar_Pervasives.Inl t), tacopt, use_eq);
                   FStarC_Syntax_Syntax.eff_opt =
                     FStar_Pervasives_Native.None
                 }) FStarC_Compiler_Range_Type.dummyRange in
          ret uu___
      | FStarC_Reflection_V1_Data.Tv_AscribedC (e, c, tacopt, use_eq) ->
          let uu___ =
            FStarC_Syntax_Syntax.mk
              (FStarC_Syntax_Syntax.Tm_ascribed
                 {
                   FStarC_Syntax_Syntax.tm = e;
                   FStarC_Syntax_Syntax.asc =
                     ((FStar_Pervasives.Inr c), tacopt, use_eq);
                   FStarC_Syntax_Syntax.eff_opt =
                     FStar_Pervasives_Native.None
                 }) FStarC_Compiler_Range_Type.dummyRange in
          ret uu___
      | FStarC_Reflection_V1_Data.Tv_Unknown ->
          let uu___ =
            FStarC_Syntax_Syntax.mk FStarC_Syntax_Syntax.Tm_unknown
              FStarC_Compiler_Range_Type.dummyRange in
          ret uu___
      | FStarC_Reflection_V1_Data.Tv_Unsupp ->
          FStarC_Tactics_Monad.fail "cannot pack Tv_Unsupp"
let (pack :
  FStarC_Reflection_V1_Data.term_view ->
    FStarC_Syntax_Syntax.term FStarC_Tactics_Monad.tac)
  = fun tv -> pack' tv false
let (pack_curried :
  FStarC_Reflection_V1_Data.term_view ->
    FStarC_Syntax_Syntax.term FStarC_Tactics_Monad.tac)
  = fun tv -> pack' tv true
let (lget :
  FStarC_Syntax_Syntax.typ ->
    Prims.string -> FStarC_Syntax_Syntax.term FStarC_Tactics_Monad.tac)
  =
  fun ty ->
    fun k ->
      let uu___ =
        Obj.magic
          (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac ()
             () (Obj.magic FStarC_Tactics_Monad.get)
             (fun uu___1 ->
                (fun ps ->
                   let ps = Obj.magic ps in
                   let uu___1 =
                     FStarC_Compiler_Util.psmap_try_find
                       ps.FStarC_Tactics_Types.local_state k in
                   match uu___1 with
                   | FStar_Pervasives_Native.None ->
                       Obj.magic (FStarC_Tactics_Monad.fail "not found")
                   | FStar_Pervasives_Native.Some t ->
                       Obj.magic (unquote ty t)) uu___1)) in
      FStarC_Tactics_Monad.wrap_err "lget" uu___
let (lset :
  FStarC_Syntax_Syntax.typ ->
    Prims.string ->
      FStarC_Syntax_Syntax.term -> unit FStarC_Tactics_Monad.tac)
  =
  fun _ty ->
    fun k ->
      fun t ->
        let uu___ =
          FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
            (Obj.magic FStarC_Tactics_Monad.get)
            (fun uu___1 ->
               (fun ps ->
                  let ps = Obj.magic ps in
                  let ps1 =
                    let uu___1 =
                      FStarC_Compiler_Util.psmap_add
                        ps.FStarC_Tactics_Types.local_state k t in
                    {
                      FStarC_Tactics_Types.main_context =
                        (ps.FStarC_Tactics_Types.main_context);
                      FStarC_Tactics_Types.all_implicits =
                        (ps.FStarC_Tactics_Types.all_implicits);
                      FStarC_Tactics_Types.goals =
                        (ps.FStarC_Tactics_Types.goals);
                      FStarC_Tactics_Types.smt_goals =
                        (ps.FStarC_Tactics_Types.smt_goals);
                      FStarC_Tactics_Types.depth =
                        (ps.FStarC_Tactics_Types.depth);
                      FStarC_Tactics_Types.__dump =
                        (ps.FStarC_Tactics_Types.__dump);
                      FStarC_Tactics_Types.psc =
                        (ps.FStarC_Tactics_Types.psc);
                      FStarC_Tactics_Types.entry_range =
                        (ps.FStarC_Tactics_Types.entry_range);
                      FStarC_Tactics_Types.guard_policy =
                        (ps.FStarC_Tactics_Types.guard_policy);
                      FStarC_Tactics_Types.freshness =
                        (ps.FStarC_Tactics_Types.freshness);
                      FStarC_Tactics_Types.tac_verb_dbg =
                        (ps.FStarC_Tactics_Types.tac_verb_dbg);
                      FStarC_Tactics_Types.local_state = uu___1;
                      FStarC_Tactics_Types.urgency =
                        (ps.FStarC_Tactics_Types.urgency);
                      FStarC_Tactics_Types.dump_on_failure =
                        (ps.FStarC_Tactics_Types.dump_on_failure)
                    } in
                  Obj.magic (FStarC_Tactics_Monad.set ps1)) uu___1) in
        FStarC_Tactics_Monad.wrap_err "lset" uu___
let (set_urgency : FStarC_BigInt.t -> unit FStarC_Tactics_Monad.tac) =
  fun u ->
    FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
      (Obj.magic FStarC_Tactics_Monad.get)
      (fun uu___ ->
         (fun ps ->
            let ps = Obj.magic ps in
            let ps1 =
              let uu___ = FStarC_BigInt.to_int_fs u in
              {
                FStarC_Tactics_Types.main_context =
                  (ps.FStarC_Tactics_Types.main_context);
                FStarC_Tactics_Types.all_implicits =
                  (ps.FStarC_Tactics_Types.all_implicits);
                FStarC_Tactics_Types.goals = (ps.FStarC_Tactics_Types.goals);
                FStarC_Tactics_Types.smt_goals =
                  (ps.FStarC_Tactics_Types.smt_goals);
                FStarC_Tactics_Types.depth = (ps.FStarC_Tactics_Types.depth);
                FStarC_Tactics_Types.__dump =
                  (ps.FStarC_Tactics_Types.__dump);
                FStarC_Tactics_Types.psc = (ps.FStarC_Tactics_Types.psc);
                FStarC_Tactics_Types.entry_range =
                  (ps.FStarC_Tactics_Types.entry_range);
                FStarC_Tactics_Types.guard_policy =
                  (ps.FStarC_Tactics_Types.guard_policy);
                FStarC_Tactics_Types.freshness =
                  (ps.FStarC_Tactics_Types.freshness);
                FStarC_Tactics_Types.tac_verb_dbg =
                  (ps.FStarC_Tactics_Types.tac_verb_dbg);
                FStarC_Tactics_Types.local_state =
                  (ps.FStarC_Tactics_Types.local_state);
                FStarC_Tactics_Types.urgency = uu___;
                FStarC_Tactics_Types.dump_on_failure =
                  (ps.FStarC_Tactics_Types.dump_on_failure)
              } in
            Obj.magic (FStarC_Tactics_Monad.set ps1)) uu___)
let (t_commute_applied_match : unit -> unit FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
        (Obj.magic FStarC_Tactics_Monad.cur_goal)
        (fun uu___2 ->
           (fun g ->
              let g = Obj.magic g in
              let uu___2 =
                let uu___3 = FStarC_Tactics_Types.goal_env g in
                let uu___4 = FStarC_Tactics_Types.goal_type g in
                destruct_eq uu___3 uu___4 in
              match uu___2 with
              | FStar_Pervasives_Native.Some (l, r) ->
                  let uu___3 = FStarC_Syntax_Util.head_and_args_full l in
                  (match uu___3 with
                   | (lh, las) ->
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = FStarC_Syntax_Util.unascribe lh in
                           FStarC_Syntax_Subst.compress uu___6 in
                         uu___5.FStarC_Syntax_Syntax.n in
                       (match uu___4 with
                        | FStarC_Syntax_Syntax.Tm_match
                            { FStarC_Syntax_Syntax.scrutinee = e;
                              FStarC_Syntax_Syntax.ret_opt = asc_opt;
                              FStarC_Syntax_Syntax.brs = brs;
                              FStarC_Syntax_Syntax.rc_opt1 = lopt;_}
                            ->
                            let brs' =
                              FStarC_Compiler_List.map
                                (fun uu___5 ->
                                   match uu___5 with
                                   | (p, w, e1) ->
                                       let uu___6 =
                                         FStarC_Syntax_Util.mk_app e1 las in
                                       (p, w, uu___6)) brs in
                            let lopt' =
                              FStarC_Compiler_Util.map_option
                                (fun rc ->
                                   let uu___5 =
                                     FStarC_Compiler_Util.map_option
                                       (fun t ->
                                          let uu___6 =
                                            let uu___7 =
                                              FStarC_Tactics_Types.goal_env g in
                                            FStarC_TypeChecker_Normalize.get_n_binders
                                              uu___7
                                              (FStarC_Compiler_List.length
                                                 las) t in
                                          match uu___6 with
                                          | (bs, c) ->
                                              let uu___7 =
                                                FStarC_Syntax_Subst.open_comp
                                                  bs c in
                                              (match uu___7 with
                                               | (bs1, c1) ->
                                                   let ss =
                                                     FStarC_Compiler_List.map2
                                                       (fun b ->
                                                          fun a ->
                                                            FStarC_Syntax_Syntax.NT
                                                              ((b.FStarC_Syntax_Syntax.binder_bv),
                                                                (FStar_Pervasives_Native.fst
                                                                   a))) bs1
                                                       las in
                                                   let c2 =
                                                     FStarC_Syntax_Subst.subst_comp
                                                       ss c1 in
                                                   FStarC_Syntax_Util.comp_result
                                                     c2))
                                       rc.FStarC_Syntax_Syntax.residual_typ in
                                   {
                                     FStarC_Syntax_Syntax.residual_effect =
                                       (rc.FStarC_Syntax_Syntax.residual_effect);
                                     FStarC_Syntax_Syntax.residual_typ =
                                       uu___5;
                                     FStarC_Syntax_Syntax.residual_flags =
                                       (rc.FStarC_Syntax_Syntax.residual_flags)
                                   }) lopt in
                            let l' =
                              FStarC_Syntax_Syntax.mk
                                (FStarC_Syntax_Syntax.Tm_match
                                   {
                                     FStarC_Syntax_Syntax.scrutinee = e;
                                     FStarC_Syntax_Syntax.ret_opt = asc_opt;
                                     FStarC_Syntax_Syntax.brs = brs';
                                     FStarC_Syntax_Syntax.rc_opt1 = lopt'
                                   }) l.FStarC_Syntax_Syntax.pos in
                            let must_tot = true in
                            let uu___5 =
                              let uu___6 = FStarC_Tactics_Types.goal_env g in
                              do_unify_maybe_guards false must_tot uu___6 l'
                                r in
                            Obj.magic
                              (FStarC_Class_Monad.op_let_Bang
                                 FStarC_Tactics_Monad.monad_tac () ()
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    (fun uu___6 ->
                                       let uu___6 = Obj.magic uu___6 in
                                       match uu___6 with
                                       | FStar_Pervasives_Native.None ->
                                           Obj.magic
                                             (FStarC_Tactics_Monad.fail
                                                "discharging the equality failed")
                                       | FStar_Pervasives_Native.Some guard
                                           ->
                                           let uu___7 =
                                             FStarC_TypeChecker_Env.is_trivial_guard_formula
                                               guard in
                                           if uu___7
                                           then
                                             (mark_uvar_as_already_checked
                                                g.FStarC_Tactics_Types.goal_ctx_uvar;
                                              Obj.magic
                                                (solve g
                                                   FStarC_Syntax_Util.exp_unit))
                                           else
                                             Obj.magic
                                               (failwith
                                                  "internal error: _t_refl: guard is not trivial"))
                                      uu___6))
                        | uu___5 ->
                            Obj.magic
                              (FStarC_Tactics_Monad.fail "lhs is not a match")))
              | FStar_Pervasives_Native.None ->
                  Obj.magic (FStarC_Tactics_Monad.fail "not an equality"))
             uu___2) in
    FStarC_Tactics_Monad.wrap_err "t_commute_applied_match" uu___1
let (string_to_term :
  env -> Prims.string -> FStarC_Syntax_Syntax.term FStarC_Tactics_Monad.tac)
  =
  fun e ->
    fun s ->
      let frag_of_text s1 =
        {
          FStarC_Parser_ParseIt.frag_fname = "<string_to_term>";
          FStarC_Parser_ParseIt.frag_text = s1;
          FStarC_Parser_ParseIt.frag_line = Prims.int_one;
          FStarC_Parser_ParseIt.frag_col = Prims.int_zero
        } in
      let uu___ =
        FStarC_Parser_ParseIt.parse FStar_Pervasives_Native.None
          (FStarC_Parser_ParseIt.Fragment (frag_of_text s)) in
      match uu___ with
      | FStarC_Parser_ParseIt.Term t ->
          let dsenv =
            let uu___1 = FStarC_TypeChecker_Env.current_module e in
            FStarC_Syntax_DsEnv.set_current_module
              e.FStarC_TypeChecker_Env.dsenv uu___1 in
          (try
             (fun uu___1 ->
                match () with
                | () ->
                    let uu___2 =
                      FStarC_ToSyntax_ToSyntax.desugar_term dsenv t in
                    ret uu___2) ()
           with
           | FStarC_Errors.Error (uu___2, e1, uu___3, uu___4) ->
               let uu___5 =
                 let uu___6 = FStarC_Errors_Msg.rendermsg e1 in
                 Prims.strcat "string_to_term: " uu___6 in
               FStarC_Tactics_Monad.fail uu___5
           | uu___2 ->
               FStarC_Tactics_Monad.fail "string_to_term: Unknown error")
      | FStarC_Parser_ParseIt.ASTFragment uu___1 ->
          FStarC_Tactics_Monad.fail
            "string_to_term: expected a Term as a result, got an ASTFragment"
      | FStarC_Parser_ParseIt.ParseError (uu___1, err, uu___2) ->
          let uu___3 =
            let uu___4 = FStarC_Errors_Msg.rendermsg err in
            Prims.strcat "string_to_term: got error " uu___4 in
          FStarC_Tactics_Monad.fail uu___3
let (push_bv_dsenv :
  env ->
    Prims.string -> (env * FStarC_Syntax_Syntax.bv) FStarC_Tactics_Monad.tac)
  =
  fun e ->
    fun i ->
      let ident =
        FStarC_Ident.mk_ident (i, FStarC_Compiler_Range_Type.dummyRange) in
      let uu___ =
        FStarC_Syntax_DsEnv.push_bv e.FStarC_TypeChecker_Env.dsenv ident in
      match uu___ with
      | (dsenv, bv) ->
          ret
            ({
               FStarC_TypeChecker_Env.solver =
                 (e.FStarC_TypeChecker_Env.solver);
               FStarC_TypeChecker_Env.range =
                 (e.FStarC_TypeChecker_Env.range);
               FStarC_TypeChecker_Env.curmodule =
                 (e.FStarC_TypeChecker_Env.curmodule);
               FStarC_TypeChecker_Env.gamma =
                 (e.FStarC_TypeChecker_Env.gamma);
               FStarC_TypeChecker_Env.gamma_sig =
                 (e.FStarC_TypeChecker_Env.gamma_sig);
               FStarC_TypeChecker_Env.gamma_cache =
                 (e.FStarC_TypeChecker_Env.gamma_cache);
               FStarC_TypeChecker_Env.modules =
                 (e.FStarC_TypeChecker_Env.modules);
               FStarC_TypeChecker_Env.expected_typ =
                 (e.FStarC_TypeChecker_Env.expected_typ);
               FStarC_TypeChecker_Env.sigtab =
                 (e.FStarC_TypeChecker_Env.sigtab);
               FStarC_TypeChecker_Env.attrtab =
                 (e.FStarC_TypeChecker_Env.attrtab);
               FStarC_TypeChecker_Env.instantiate_imp =
                 (e.FStarC_TypeChecker_Env.instantiate_imp);
               FStarC_TypeChecker_Env.effects =
                 (e.FStarC_TypeChecker_Env.effects);
               FStarC_TypeChecker_Env.generalize =
                 (e.FStarC_TypeChecker_Env.generalize);
               FStarC_TypeChecker_Env.letrecs =
                 (e.FStarC_TypeChecker_Env.letrecs);
               FStarC_TypeChecker_Env.top_level =
                 (e.FStarC_TypeChecker_Env.top_level);
               FStarC_TypeChecker_Env.check_uvars =
                 (e.FStarC_TypeChecker_Env.check_uvars);
               FStarC_TypeChecker_Env.use_eq_strict =
                 (e.FStarC_TypeChecker_Env.use_eq_strict);
               FStarC_TypeChecker_Env.is_iface =
                 (e.FStarC_TypeChecker_Env.is_iface);
               FStarC_TypeChecker_Env.admit =
                 (e.FStarC_TypeChecker_Env.admit);
               FStarC_TypeChecker_Env.lax_universes =
                 (e.FStarC_TypeChecker_Env.lax_universes);
               FStarC_TypeChecker_Env.phase1 =
                 (e.FStarC_TypeChecker_Env.phase1);
               FStarC_TypeChecker_Env.failhard =
                 (e.FStarC_TypeChecker_Env.failhard);
               FStarC_TypeChecker_Env.flychecking =
                 (e.FStarC_TypeChecker_Env.flychecking);
               FStarC_TypeChecker_Env.uvar_subtyping =
                 (e.FStarC_TypeChecker_Env.uvar_subtyping);
               FStarC_TypeChecker_Env.intactics =
                 (e.FStarC_TypeChecker_Env.intactics);
               FStarC_TypeChecker_Env.nocoerce =
                 (e.FStarC_TypeChecker_Env.nocoerce);
               FStarC_TypeChecker_Env.tc_term =
                 (e.FStarC_TypeChecker_Env.tc_term);
               FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                 (e.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
               FStarC_TypeChecker_Env.universe_of =
                 (e.FStarC_TypeChecker_Env.universe_of);
               FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                 (e.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
               FStarC_TypeChecker_Env.teq_nosmt_force =
                 (e.FStarC_TypeChecker_Env.teq_nosmt_force);
               FStarC_TypeChecker_Env.subtype_nosmt_force =
                 (e.FStarC_TypeChecker_Env.subtype_nosmt_force);
               FStarC_TypeChecker_Env.qtbl_name_and_index =
                 (e.FStarC_TypeChecker_Env.qtbl_name_and_index);
               FStarC_TypeChecker_Env.normalized_eff_names =
                 (e.FStarC_TypeChecker_Env.normalized_eff_names);
               FStarC_TypeChecker_Env.fv_delta_depths =
                 (e.FStarC_TypeChecker_Env.fv_delta_depths);
               FStarC_TypeChecker_Env.proof_ns =
                 (e.FStarC_TypeChecker_Env.proof_ns);
               FStarC_TypeChecker_Env.synth_hook =
                 (e.FStarC_TypeChecker_Env.synth_hook);
               FStarC_TypeChecker_Env.try_solve_implicits_hook =
                 (e.FStarC_TypeChecker_Env.try_solve_implicits_hook);
               FStarC_TypeChecker_Env.splice =
                 (e.FStarC_TypeChecker_Env.splice);
               FStarC_TypeChecker_Env.mpreprocess =
                 (e.FStarC_TypeChecker_Env.mpreprocess);
               FStarC_TypeChecker_Env.postprocess =
                 (e.FStarC_TypeChecker_Env.postprocess);
               FStarC_TypeChecker_Env.identifier_info =
                 (e.FStarC_TypeChecker_Env.identifier_info);
               FStarC_TypeChecker_Env.tc_hooks =
                 (e.FStarC_TypeChecker_Env.tc_hooks);
               FStarC_TypeChecker_Env.dsenv = dsenv;
               FStarC_TypeChecker_Env.nbe = (e.FStarC_TypeChecker_Env.nbe);
               FStarC_TypeChecker_Env.strict_args_tab =
                 (e.FStarC_TypeChecker_Env.strict_args_tab);
               FStarC_TypeChecker_Env.erasable_types_tab =
                 (e.FStarC_TypeChecker_Env.erasable_types_tab);
               FStarC_TypeChecker_Env.enable_defer_to_tac =
                 (e.FStarC_TypeChecker_Env.enable_defer_to_tac);
               FStarC_TypeChecker_Env.unif_allow_ref_guards =
                 (e.FStarC_TypeChecker_Env.unif_allow_ref_guards);
               FStarC_TypeChecker_Env.erase_erasable_args =
                 (e.FStarC_TypeChecker_Env.erase_erasable_args);
               FStarC_TypeChecker_Env.core_check =
                 (e.FStarC_TypeChecker_Env.core_check);
               FStarC_TypeChecker_Env.missing_decl =
                 (e.FStarC_TypeChecker_Env.missing_decl)
             }, bv)
let (term_to_string :
  FStarC_Syntax_Syntax.term -> Prims.string FStarC_Tactics_Monad.tac) =
  fun t ->
    let s = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
    ret s
let (comp_to_string :
  FStarC_Syntax_Syntax.comp -> Prims.string FStarC_Tactics_Monad.tac) =
  fun c ->
    let s = FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp c in
    ret s
let (range_to_string :
  FStarC_Compiler_Range_Type.range -> Prims.string FStarC_Tactics_Monad.tac)
  =
  fun r ->
    let uu___ =
      FStarC_Class_Show.show FStarC_Compiler_Range_Ops.showable_range r in
    ret uu___
let (term_eq_old :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.term -> Prims.bool FStarC_Tactics_Monad.tac)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t1 ->
         fun t2 ->
           Obj.magic
             (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac
                () () idtac
                (fun uu___ ->
                   (fun uu___ ->
                      let uu___ = Obj.magic uu___ in
                      let uu___1 = FStarC_Syntax_Util.term_eq t1 t2 in
                      Obj.magic (ret uu___1)) uu___))) uu___1 uu___
let with_compat_pre_core :
  'a .
    FStarC_BigInt.t ->
      'a FStarC_Tactics_Monad.tac -> 'a FStarC_Tactics_Monad.tac
  =
  fun n ->
    fun f ->
      FStarC_Tactics_Monad.mk_tac
        (fun ps ->
           FStarC_Options.with_saved_options
             (fun uu___ ->
                let _res = FStarC_Options.set_options "--compat_pre_core 0" in
                FStarC_Tactics_Monad.run f ps))
let (get_vconfig : unit -> FStarC_VConfig.vconfig FStarC_Tactics_Monad.tac) =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
            (Obj.magic FStarC_Tactics_Monad.cur_goal)
            (fun uu___1 ->
               (fun g ->
                  let g = Obj.magic g in
                  let vcfg =
                    FStarC_Options.with_saved_options
                      (fun uu___1 ->
                         FStarC_Options.set g.FStarC_Tactics_Types.opts;
                         FStarC_Options.get_vconfig ()) in
                  Obj.magic (ret vcfg)) uu___1))) uu___
let (set_vconfig : FStarC_VConfig.vconfig -> unit FStarC_Tactics_Monad.tac) =
  fun vcfg ->
    FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
      (Obj.magic FStarC_Tactics_Monad.cur_goal)
      (fun uu___ ->
         (fun g ->
            let g = Obj.magic g in
            let opts' =
              FStarC_Options.with_saved_options
                (fun uu___ ->
                   FStarC_Options.set g.FStarC_Tactics_Types.opts;
                   FStarC_Options.set_vconfig vcfg;
                   FStarC_Options.peek ()) in
            let g' =
              {
                FStarC_Tactics_Types.goal_main_env =
                  (g.FStarC_Tactics_Types.goal_main_env);
                FStarC_Tactics_Types.goal_ctx_uvar =
                  (g.FStarC_Tactics_Types.goal_ctx_uvar);
                FStarC_Tactics_Types.opts = opts';
                FStarC_Tactics_Types.is_guard =
                  (g.FStarC_Tactics_Types.is_guard);
                FStarC_Tactics_Types.label = (g.FStarC_Tactics_Types.label)
              } in
            Obj.magic (FStarC_Tactics_Monad.replace_cur g')) uu___)
let (t_smt_sync : FStarC_VConfig.vconfig -> unit FStarC_Tactics_Monad.tac) =
  fun vcfg ->
    let uu___ =
      FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
        (Obj.magic FStarC_Tactics_Monad.cur_goal)
        (fun uu___1 ->
           (fun goal ->
              let goal = Obj.magic goal in
              let uu___1 = get_phi goal in
              match uu___1 with
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (FStarC_Tactics_Monad.fail "Goal is not irrelevant")
              | FStar_Pervasives_Native.Some phi ->
                  let e = FStarC_Tactics_Types.goal_env goal in
                  let ans =
                    FStarC_Options.with_saved_options
                      (fun uu___2 ->
                         FStarC_Options.set_vconfig vcfg;
                         (e.FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.solve_sync
                           FStar_Pervasives_Native.None e phi) in
                  if ans
                  then
                    (mark_uvar_as_already_checked
                       goal.FStarC_Tactics_Types.goal_ctx_uvar;
                     Obj.magic (solve goal FStarC_Syntax_Util.exp_unit))
                  else
                    Obj.magic
                      (FStarC_Tactics_Monad.fail
                         "SMT did not solve this goal")) uu___1) in
    FStarC_Tactics_Monad.wrap_err "t_smt_sync" uu___
let (free_uvars :
  FStarC_Syntax_Syntax.term ->
    FStarC_BigInt.t Prims.list FStarC_Tactics_Monad.tac)
  =
  fun uu___ ->
    (fun tm ->
       Obj.magic
         (FStarC_Class_Monad.op_let_Bang FStarC_Tactics_Monad.monad_tac () ()
            idtac
            (fun uu___ ->
               (fun uu___ ->
                  let uu___ = Obj.magic uu___ in
                  let uvs =
                    let uu___1 =
                      let uu___2 = FStarC_Syntax_Free.uvars_uncached tm in
                      FStarC_Class_Setlike.elems ()
                        (Obj.magic
                           (FStarC_Compiler_FlatSet.setlike_flat_set
                              FStarC_Syntax_Free.ord_ctx_uvar))
                        (Obj.magic uu___2) in
                    FStarC_Compiler_List.map
                      (fun u ->
                         let uu___2 =
                           FStarC_Syntax_Unionfind.uvar_id
                             u.FStarC_Syntax_Syntax.ctx_uvar_head in
                         FStarC_BigInt.of_int_fs uu___2) uu___1 in
                  Obj.magic (ret uvs)) uu___))) uu___
let (dbg_refl : env -> (unit -> Prims.string) -> unit) =
  fun g ->
    fun msg ->
      let uu___ = FStarC_Compiler_Effect.op_Bang dbg_ReflTc in
      if uu___
      then let uu___1 = msg () in FStarC_Compiler_Util.print_string uu___1
      else ()
type issues = FStarC_Errors.issue Prims.list
let refl_typing_builtin_wrapper :
  'a .
    (unit -> 'a) ->
      ('a FStar_Pervasives_Native.option * issues) FStarC_Tactics_Monad.tac
  =
  fun f ->
    let tx = FStarC_Syntax_Unionfind.new_transaction () in
    let uu___ =
      try
        (fun uu___1 ->
           match () with | () -> FStarC_Errors.catch_errors_and_ignore_rest f)
          ()
      with
      | uu___1 ->
          let issue =
            let uu___2 =
              let uu___3 = FStarC_Compiler_Util.print_exn uu___1 in
              FStarC_Errors_Msg.mkmsg uu___3 in
            let uu___3 = FStarC_Errors.get_ctx () in
            {
              FStarC_Errors.issue_msg = uu___2;
              FStarC_Errors.issue_level = FStarC_Errors.EError;
              FStarC_Errors.issue_range = FStar_Pervasives_Native.None;
              FStarC_Errors.issue_number =
                (FStar_Pervasives_Native.Some (Prims.of_int (17)));
              FStarC_Errors.issue_ctx = uu___3
            } in
          ([issue], FStar_Pervasives_Native.None) in
    match uu___ with
    | (errs, r) ->
        (FStarC_Syntax_Unionfind.rollback tx;
         if (FStarC_Compiler_List.length errs) > Prims.int_zero
         then ret (FStar_Pervasives_Native.None, errs)
         else ret (r, errs))
let (no_uvars_in_term : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    (let uu___ = FStarC_Syntax_Free.uvars t in
     FStarC_Class_Setlike.is_empty ()
       (Obj.magic
          (FStarC_Compiler_FlatSet.setlike_flat_set
             FStarC_Syntax_Free.ord_ctx_uvar)) (Obj.magic uu___))
      &&
      (let uu___ = FStarC_Syntax_Free.univs t in
       FStarC_Class_Setlike.is_empty ()
         (Obj.magic
            (FStarC_Compiler_FlatSet.setlike_flat_set
               FStarC_Syntax_Free.ord_univ_uvar)) (Obj.magic uu___))
let (no_uvars_in_g : env -> Prims.bool) =
  fun g ->
    FStarC_Compiler_Util.for_all
      (fun uu___ ->
         match uu___ with
         | FStarC_Syntax_Syntax.Binding_var bv ->
             no_uvars_in_term bv.FStarC_Syntax_Syntax.sort
         | uu___1 -> true) g.FStarC_TypeChecker_Env.gamma
type relation =
  | Subtyping 
  | Equality 
let (uu___is_Subtyping : relation -> Prims.bool) =
  fun projectee -> match projectee with | Subtyping -> true | uu___ -> false
let (uu___is_Equality : relation -> Prims.bool) =
  fun projectee -> match projectee with | Equality -> true | uu___ -> false
let (unexpected_uvars_issue :
  FStarC_Compiler_Range_Type.range -> FStarC_Errors.issue) =
  fun r ->
    let i =
      let uu___ = FStarC_Errors_Msg.mkmsg "Cannot check relation with uvars" in
      let uu___1 =
        let uu___2 =
          FStarC_Errors.errno
            FStarC_Errors_Codes.Error_UnexpectedUnresolvedUvar in
        FStar_Pervasives_Native.Some uu___2 in
      {
        FStarC_Errors.issue_msg = uu___;
        FStarC_Errors.issue_level = FStarC_Errors.EError;
        FStarC_Errors.issue_range = (FStar_Pervasives_Native.Some r);
        FStarC_Errors.issue_number = uu___1;
        FStarC_Errors.issue_ctx = []
      } in
    i