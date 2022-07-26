open Prims
let (core_check :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binding Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Reflection_Data.typ FStar_Pervasives_Native.option,
            FStar_TypeChecker_Core.error) FStar_Pervasives.either)
  =
  fun env ->
    fun gamma ->
      fun sol ->
        fun t ->
          let env1 =
            {
              FStar_TypeChecker_Env.solver =
                (env.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range = (env.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (env.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma = gamma;
              FStar_TypeChecker_Env.gamma_sig =
                (env.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (env.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (env.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (env.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (env.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (env.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (env.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (env.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (env.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (env.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (env.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (env.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq_strict =
                (env.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (env.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit = (env.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = (env.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (env.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (env.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (env.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (env.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (env.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (env.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
              FStar_TypeChecker_Env.universe_of =
                (env.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
              FStar_TypeChecker_Env.teq_nosmt_force =
                (env.FStar_TypeChecker_Env.teq_nosmt_force);
              FStar_TypeChecker_Env.subtype_nosmt_force =
                (env.FStar_TypeChecker_Env.subtype_nosmt_force);
              FStar_TypeChecker_Env.use_bv_sorts =
                (env.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (env.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (env.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (env.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (env.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (env.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (env.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (env.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (env.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (env.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (env.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv = (env.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe = (env.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (env.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (env.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (env.FStar_TypeChecker_Env.enable_defer_to_tac);
              FStar_TypeChecker_Env.unif_allow_ref_guards =
                (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
              FStar_TypeChecker_Env.erase_erasable_args =
                (env.FStar_TypeChecker_Env.erase_erasable_args);
              FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar =
                (env.FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar)
            } in
          let uu___ = FStar_TypeChecker_Core.check_term env1 sol t in
          match uu___ with
          | FStar_Pervasives.Inl (FStar_Pervasives_Native.None) ->
              ((let uu___2 =
                  let uu___3 = FStar_TypeChecker_Env.get_range env1 in
                  FStar_Compiler_Range.string_of_range uu___3 in
                let uu___3 = FStar_Syntax_Print.term_to_string sol in
                FStar_Compiler_Util.print2
                  "(%s) Core checking succeeded on %s\n" uu___2 uu___3);
               FStar_Pervasives.Inl FStar_Pervasives_Native.None)
          | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g) ->
              ((let uu___2 =
                  let uu___3 = FStar_TypeChecker_Env.get_range env1 in
                  FStar_Compiler_Range.string_of_range uu___3 in
                let uu___3 = FStar_Syntax_Print.term_to_string sol in
                let uu___4 = FStar_Syntax_Print.term_to_string g in
                FStar_Compiler_Util.print3
                  "(%s) Core checking succeeded on %s, with guard %s\n"
                  uu___2 uu___3 uu___4);
               FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g))
          | FStar_Pervasives.Inr err ->
              ((let uu___2 =
                  let uu___3 = FStar_TypeChecker_Env.get_range env1 in
                  FStar_Compiler_Range.string_of_range uu___3 in
                let uu___3 = FStar_Syntax_Print.term_to_string sol in
                let uu___4 = FStar_TypeChecker_Core.print_error err in
                FStar_Compiler_Util.print3
                  "(%s) Core checking failed on term %s\n%s\n" uu___2 uu___3
                  uu___4);
               FStar_Pervasives.Inr err)
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (rangeof : FStar_Tactics_Types.goal -> FStar_Compiler_Range.range) =
  fun g ->
    (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_range
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
let (set_uvar_expected_typ :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Reflection_Data.typ -> unit) =
  fun u ->
    fun t ->
      let dec =
        FStar_Syntax_Unionfind.find_decoration
          u.FStar_Syntax_Syntax.ctx_uvar_head in
      FStar_Syntax_Unionfind.change_decoration
        u.FStar_Syntax_Syntax.ctx_uvar_head
        {
          FStar_Syntax_Syntax.uvar_decoration_typ = t;
          FStar_Syntax_Syntax.uvar_decoration_should_check =
            (dec.FStar_Syntax_Syntax.uvar_decoration_should_check)
        }
let (mark_uvar_as_allow_untyped : FStar_Syntax_Syntax.ctx_uvar -> unit) =
  fun u ->
    let dec =
      FStar_Syntax_Unionfind.find_decoration
        u.FStar_Syntax_Syntax.ctx_uvar_head in
    FStar_Syntax_Unionfind.change_decoration
      u.FStar_Syntax_Syntax.ctx_uvar_head
      {
        FStar_Syntax_Syntax.uvar_decoration_typ =
          (dec.FStar_Syntax_Syntax.uvar_decoration_typ);
        FStar_Syntax_Syntax.uvar_decoration_should_check =
          FStar_Syntax_Syntax.Allow_untyped
      }
let (mark_goal_implicit_allow_untyped : FStar_Tactics_Types.goal -> unit) =
  fun g -> mark_uvar_as_allow_untyped g.FStar_Tactics_Types.goal_ctx_uvar
let (goal_with_type :
  FStar_Tactics_Types.goal ->
    FStar_Reflection_Data.typ -> FStar_Tactics_Types.goal)
  =
  fun g ->
    fun t ->
      let u = g.FStar_Tactics_Types.goal_ctx_uvar in
      set_uvar_expected_typ u t; g
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g ->
    let uu___ =
      let uu___1 = FStar_Tactics_Types.goal_env g in
      let uu___2 = FStar_Tactics_Types.goal_type g in bnorm uu___1 uu___2 in
    goal_with_type g uu___
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
    FStar_Tactics_Monad.ret ()
let (debugging : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let uu___1 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac") in
         FStar_Tactics_Monad.ret uu___1)
let (do_dump_ps : Prims.string -> FStar_Tactics_Types.proofstate -> unit) =
  fun msg ->
    fun ps ->
      let psc = ps.FStar_Tactics_Types.psc in
      let subst = FStar_TypeChecker_Cfg.psc_subst psc in
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
             FStar_Compiler_Effect.op_Bar_Greater uu___
               FStar_Compiler_Util.set_elements in
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
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu___ = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu___ with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
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
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu___ = destruct_eq' typ in
    match uu___ with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None ->
        let uu___1 = FStar_Syntax_Util.un_squash typ in
        (match uu___1 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (__do_unify_wflags :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
              FStar_Tactics_Monad.tac)
  =
  fun dbg ->
    fun allow_guards ->
      fun env1 ->
        fun t1 ->
          fun t2 ->
            if dbg
            then
              (let uu___1 = FStar_Syntax_Print.term_to_string t1 in
               let uu___2 = FStar_Syntax_Print.term_to_string t2 in
               FStar_Compiler_Util.print2 "%%%%%%%%do_unify %s =? %s\n"
                 uu___1 uu___2)
            else ();
            (let uu___1 =
               FStar_Tactics_Monad.trytac FStar_Tactics_Monad.cur_goal in
             FStar_Tactics_Monad.bind uu___1
               (fun gopt ->
                  try
                    (fun uu___2 ->
                       match () with
                       | () ->
                           let res =
                             let env2 =
                               let uu___3 =
                                 FStar_Compiler_Effect.op_Bar_Greater gopt
                                   (FStar_Compiler_Util.map_option
                                      (fun g ->
                                         let uu___4 =
                                           FStar_Compiler_Effect.op_Bar_Greater
                                             g.FStar_Tactics_Types.goal_ctx_uvar
                                             (fun uu___5 ->
                                                FStar_Pervasives_Native.Some
                                                  uu___5) in
                                         {
                                           FStar_TypeChecker_Env.solver =
                                             (env1.FStar_TypeChecker_Env.solver);
                                           FStar_TypeChecker_Env.range =
                                             (env1.FStar_TypeChecker_Env.range);
                                           FStar_TypeChecker_Env.curmodule =
                                             (env1.FStar_TypeChecker_Env.curmodule);
                                           FStar_TypeChecker_Env.gamma =
                                             (env1.FStar_TypeChecker_Env.gamma);
                                           FStar_TypeChecker_Env.gamma_sig =
                                             (env1.FStar_TypeChecker_Env.gamma_sig);
                                           FStar_TypeChecker_Env.gamma_cache
                                             =
                                             (env1.FStar_TypeChecker_Env.gamma_cache);
                                           FStar_TypeChecker_Env.modules =
                                             (env1.FStar_TypeChecker_Env.modules);
                                           FStar_TypeChecker_Env.expected_typ
                                             =
                                             (env1.FStar_TypeChecker_Env.expected_typ);
                                           FStar_TypeChecker_Env.sigtab =
                                             (env1.FStar_TypeChecker_Env.sigtab);
                                           FStar_TypeChecker_Env.attrtab =
                                             (env1.FStar_TypeChecker_Env.attrtab);
                                           FStar_TypeChecker_Env.instantiate_imp
                                             =
                                             (env1.FStar_TypeChecker_Env.instantiate_imp);
                                           FStar_TypeChecker_Env.effects =
                                             (env1.FStar_TypeChecker_Env.effects);
                                           FStar_TypeChecker_Env.generalize =
                                             (env1.FStar_TypeChecker_Env.generalize);
                                           FStar_TypeChecker_Env.letrecs =
                                             (env1.FStar_TypeChecker_Env.letrecs);
                                           FStar_TypeChecker_Env.top_level =
                                             (env1.FStar_TypeChecker_Env.top_level);
                                           FStar_TypeChecker_Env.check_uvars
                                             =
                                             (env1.FStar_TypeChecker_Env.check_uvars);
                                           FStar_TypeChecker_Env.use_eq_strict
                                             =
                                             (env1.FStar_TypeChecker_Env.use_eq_strict);
                                           FStar_TypeChecker_Env.is_iface =
                                             (env1.FStar_TypeChecker_Env.is_iface);
                                           FStar_TypeChecker_Env.admit =
                                             (env1.FStar_TypeChecker_Env.admit);
                                           FStar_TypeChecker_Env.lax =
                                             (env1.FStar_TypeChecker_Env.lax);
                                           FStar_TypeChecker_Env.lax_universes
                                             =
                                             (env1.FStar_TypeChecker_Env.lax_universes);
                                           FStar_TypeChecker_Env.phase1 =
                                             (env1.FStar_TypeChecker_Env.phase1);
                                           FStar_TypeChecker_Env.failhard =
                                             (env1.FStar_TypeChecker_Env.failhard);
                                           FStar_TypeChecker_Env.nosynth =
                                             (env1.FStar_TypeChecker_Env.nosynth);
                                           FStar_TypeChecker_Env.uvar_subtyping
                                             =
                                             (env1.FStar_TypeChecker_Env.uvar_subtyping);
                                           FStar_TypeChecker_Env.tc_term =
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
                                           FStar_TypeChecker_Env.use_bv_sorts
                                             =
                                             (env1.FStar_TypeChecker_Env.use_bv_sorts);
                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                             =
                                             (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                                           FStar_TypeChecker_Env.normalized_eff_names
                                             =
                                             (env1.FStar_TypeChecker_Env.normalized_eff_names);
                                           FStar_TypeChecker_Env.fv_delta_depths
                                             =
                                             (env1.FStar_TypeChecker_Env.fv_delta_depths);
                                           FStar_TypeChecker_Env.proof_ns =
                                             (env1.FStar_TypeChecker_Env.proof_ns);
                                           FStar_TypeChecker_Env.synth_hook =
                                             (env1.FStar_TypeChecker_Env.synth_hook);
                                           FStar_TypeChecker_Env.try_solve_implicits_hook
                                             =
                                             (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                           FStar_TypeChecker_Env.splice =
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
                                           FStar_TypeChecker_Env.tc_hooks =
                                             (env1.FStar_TypeChecker_Env.tc_hooks);
                                           FStar_TypeChecker_Env.dsenv =
                                             (env1.FStar_TypeChecker_Env.dsenv);
                                           FStar_TypeChecker_Env.nbe =
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
                                           FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar
                                             = uu___4
                                         })) in
                               FStar_Compiler_Effect.op_Bar_Greater uu___3
                                 (FStar_Compiler_Util.dflt env1) in
                             if allow_guards
                             then
                               FStar_TypeChecker_Rel.try_teq true env2 t1 t2
                             else FStar_TypeChecker_Rel.teq_nosmt env2 t1 t2 in
                           (if dbg
                            then
                              (let uu___4 =
                                 FStar_Common.string_of_option
                                   (FStar_TypeChecker_Rel.guard_to_string
                                      env1) res in
                               let uu___5 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu___6 =
                                 FStar_Syntax_Print.term_to_string t2 in
                               FStar_Compiler_Util.print3
                                 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                                 uu___4 uu___5 uu___6)
                            else ();
                            (match res with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Tactics_Monad.ret
                                   FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some g ->
                                 let uu___4 =
                                   FStar_Tactics_Monad.add_implicits
                                     g.FStar_TypeChecker_Common.implicits in
                                 FStar_Tactics_Monad.bind uu___4
                                   (fun uu___5 ->
                                      FStar_Tactics_Monad.ret
                                        (FStar_Pervasives_Native.Some g)))))
                      ()
                  with
                  | FStar_Errors.Err (uu___3, msg, uu___4) ->
                      FStar_Tactics_Monad.mlog
                        (fun uu___5 ->
                           FStar_Compiler_Util.print1
                             ">> do_unify error, (%s)\n" msg)
                        (fun uu___5 ->
                           FStar_Tactics_Monad.ret
                             FStar_Pervasives_Native.None)
                  | FStar_Errors.Error (uu___3, msg, r, uu___4) ->
                      FStar_Tactics_Monad.mlog
                        (fun uu___5 ->
                           let uu___6 =
                             FStar_Compiler_Range.string_of_range r in
                           FStar_Compiler_Util.print2
                             ">> do_unify error, (%s) at (%s)\n" msg uu___6)
                        (fun uu___5 ->
                           FStar_Tactics_Monad.ret
                             FStar_Pervasives_Native.None)))
let (__do_unify :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
            FStar_Tactics_Monad.tac)
  =
  fun allow_guards ->
    fun env1 ->
      fun t1 ->
        fun t2 ->
          let dbg =
            FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "TacUnify") in
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
            (fun uu___ ->
               if dbg
               then
                 (FStar_Options.push ();
                  (let uu___3 =
                     FStar_Options.set_options
                       "--debug_level Rel --debug_level RelCheck" in
                   ()))
               else ();
               (let uu___2 = __do_unify_wflags dbg allow_guards env1 t1 t2 in
                FStar_Tactics_Monad.bind uu___2
                  (fun r ->
                     if dbg then FStar_Options.pop () else ();
                     FStar_Tactics_Monad.ret r)))
let (do_unify :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uu___ = __do_unify false env1 t1 t2 in
        FStar_Tactics_Monad.bind uu___
          (fun uu___1 ->
             match uu___1 with
             | FStar_Pervasives_Native.None -> FStar_Tactics_Monad.ret false
             | FStar_Pervasives_Native.Some g ->
                 ((let uu___3 =
                     let uu___4 =
                       FStar_TypeChecker_Env.is_trivial_guard_formula g in
                     Prims.op_Negation uu___4 in
                   if uu___3
                   then
                     failwith
                       "internal error: do_unify: guard is not trivial"
                   else ());
                  FStar_Tactics_Monad.ret true))
let (do_unify' :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
            FStar_Tactics_Monad.tac)
  =
  fun allow_guards ->
    fun env1 -> fun t1 -> fun t2 -> __do_unify allow_guards env1 t1 t2
let (do_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          FStar_Tactics_Monad.mk_tac
            (fun ps ->
               let tx = FStar_Syntax_Unionfind.new_transaction () in
               FStar_Tactics_Result.Success (tx, ps)) in
        FStar_Tactics_Monad.bind uu___
          (fun tx ->
             let uvs1 = FStar_Syntax_Free.uvars_uncached t1 in
             let uu___1 = do_unify env1 t1 t2 in
             FStar_Tactics_Monad.bind uu___1
               (fun r ->
                  if r
                  then
                    let uvs2 = FStar_Syntax_Free.uvars_uncached t1 in
                    let uu___2 =
                      let uu___3 = FStar_Compiler_Util.set_eq uvs1 uvs2 in
                      Prims.op_Negation uu___3 in
                    (if uu___2
                     then
                       (FStar_Syntax_Unionfind.rollback tx;
                        FStar_Tactics_Monad.ret false)
                     else FStar_Tactics_Monad.ret true)
                  else FStar_Tactics_Monad.ret false))
let (do_match_on_lhs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          FStar_Tactics_Monad.mk_tac
            (fun ps ->
               let tx = FStar_Syntax_Unionfind.new_transaction () in
               FStar_Tactics_Result.Success (tx, ps)) in
        FStar_Tactics_Monad.bind uu___
          (fun tx ->
             let uu___1 = destruct_eq t1 in
             match uu___1 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "do_match_on_lhs: not an eq"
             | FStar_Pervasives_Native.Some (lhs, uu___2) ->
                 let uvs1 = FStar_Syntax_Free.uvars_uncached lhs in
                 let uu___3 = do_unify env1 t1 t2 in
                 FStar_Tactics_Monad.bind uu___3
                   (fun r ->
                      if r
                      then
                        let uvs2 = FStar_Syntax_Free.uvars_uncached lhs in
                        let uu___4 =
                          let uu___5 = FStar_Compiler_Util.set_eq uvs1 uvs2 in
                          Prims.op_Negation uu___5 in
                        (if uu___4
                         then
                           (FStar_Syntax_Unionfind.rollback tx;
                            FStar_Tactics_Monad.ret false)
                         else FStar_Tactics_Monad.ret true)
                      else FStar_Tactics_Monad.ret false))
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
           mark_goal_implicit_allow_untyped goal;
           FStar_Tactics_Monad.ret ())
let (trysolve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu___ = FStar_Tactics_Types.goal_env goal in
      let uu___1 = FStar_Tactics_Types.goal_witness goal in
      do_unify uu___ solution uu___1
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
             FStar_Syntax_Print.term_to_string uu___2 in
           let uu___2 = FStar_Syntax_Print.term_to_string solution in
           FStar_Compiler_Util.print2 "solve %s := %s\n" uu___1 uu___2)
        (fun uu___ ->
           let uu___1 = trysolve goal solution in
           FStar_Tactics_Monad.bind uu___1
             (fun b ->
                if b
                then
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu___2 -> FStar_Tactics_Monad.remove_solved_goals)
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
                     FStar_Compiler_Util.format3 "%s does not solve %s : %s"
                       uu___4 uu___5 uu___6 in
                   FStar_Tactics_Monad.fail uu___3)))
let (solve' :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu___ = set_solution goal solution in
      FStar_Tactics_Monad.bind uu___
        (fun uu___1 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
             (fun uu___2 -> FStar_Tactics_Monad.remove_solved_goals))
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
let (tadmit_t : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu___ =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                (let uu___2 =
                   let uu___3 = FStar_Tactics_Types.goal_type g in
                   uu___3.FStar_Syntax_Syntax.pos in
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       FStar_Tactics_Printing.goal_to_string ""
                         FStar_Pervasives_Native.None ps g in
                     FStar_Compiler_Util.format1
                       "Tactics admitted goal <%s>\n\n" uu___5 in
                   (FStar_Errors.Warning_TacAdmit, uu___4) in
                 FStar_Errors.log_issue uu___2 uu___3);
                solve' g t)) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "tadmit_t") uu___
let (fresh : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let n = ps.FStar_Tactics_Types.freshness in
         let ps1 =
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
             FStar_Tactics_Types.freshness = (n + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (ps.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (ps.FStar_Tactics_Types.local_state);
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
           } in
         let uu___1 = FStar_Tactics_Monad.set ps1 in
         FStar_Tactics_Monad.bind uu___1
           (fun uu___2 ->
              let uu___3 = FStar_BigInt.of_int_fs n in
              FStar_Tactics_Monad.ret uu___3))
let (curms : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStar_Compiler_Util.now_ms () in
      FStar_Compiler_Effect.op_Bar_Greater uu___2 FStar_BigInt.of_int_fs in
    FStar_Tactics_Monad.ret uu___1
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
             (fun uu___ ->
                let uu___1 = FStar_Syntax_Print.term_to_string t in
                FStar_Compiler_Util.print1 "Tac> __tc(%s)\n" uu___1)
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
                    FStar_TypeChecker_Env.lax = (e.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (e.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (e.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (e.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (e.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
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
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (e.FStar_TypeChecker_Env.use_bv_sorts);
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
                    FStar_TypeChecker_Env.dsenv =
                      (e.FStar_TypeChecker_Env.dsenv);
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
                    FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar =
                      (e.FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar)
                  } in
                try
                  (fun uu___1 ->
                     match () with
                     | () ->
                         let uu___2 =
                           FStar_TypeChecker_TcTerm.typeof_tot_or_gtot_term
                             e1 t true in
                         FStar_Tactics_Monad.ret uu___2) ()
                with
                | FStar_Errors.Err (uu___2, msg, uu___3) ->
                    let uu___4 = tts e1 t in
                    let uu___5 =
                      let uu___6 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_Compiler_Effect.op_Bar_Greater uu___6
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type (1) %s in context (%s). Error = (%s)"
                      uu___4 uu___5 msg
                | FStar_Errors.Error (uu___2, msg, uu___3, uu___4) ->
                    let uu___5 = tts e1 t in
                    let uu___6 =
                      let uu___7 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_Compiler_Effect.op_Bar_Greater uu___7
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type (1) %s in context (%s). Error = (%s)"
                      uu___5 uu___6 msg))
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
             (fun uu___ ->
                let uu___1 = FStar_Syntax_Print.term_to_string t in
                FStar_Compiler_Util.print1 "Tac> __tc_ghost(%s)\n" uu___1)
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
                    FStar_TypeChecker_Env.lax = (e.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (e.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (e.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (e.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (e.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
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
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (e.FStar_TypeChecker_Env.use_bv_sorts);
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
                    FStar_TypeChecker_Env.dsenv =
                      (e.FStar_TypeChecker_Env.dsenv);
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
                    FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar =
                      (e.FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar)
                  } in
                try
                  (fun uu___1 ->
                     match () with
                     | () ->
                         let uu___2 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t in
                         (match uu___2 with
                          | (t1, lc, g) ->
                              FStar_Tactics_Monad.ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu___2, msg, uu___3) ->
                    let uu___4 = tts e1 t in
                    let uu___5 =
                      let uu___6 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_Compiler_Effect.op_Bar_Greater uu___6
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type (2) %s in context (%s). Error = (%s)"
                      uu___4 uu___5 msg
                | FStar_Errors.Error (uu___2, msg, uu___3, uu___4) ->
                    let uu___5 = tts e1 t in
                    let uu___6 =
                      let uu___7 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_Compiler_Effect.op_Bar_Greater uu___7
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type (2) %s in context (%s). Error = (%s)"
                      uu___5 uu___6 msg))
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
             (fun uu___ ->
                let uu___1 = FStar_Syntax_Print.term_to_string t in
                let uu___2 =
                  let uu___3 = FStar_TypeChecker_Env.all_binders e in
                  FStar_Compiler_Effect.op_Bar_Greater uu___3
                    (FStar_Syntax_Print.binders_to_string ", ") in
                FStar_Compiler_Util.print2 "Tac> __tc_lax(%s)(Context:%s)\n"
                  uu___1 uu___2)
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
                    FStar_TypeChecker_Env.lax = (e.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (e.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (e.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (e.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (e.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
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
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (e.FStar_TypeChecker_Env.use_bv_sorts);
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
                    FStar_TypeChecker_Env.dsenv =
                      (e.FStar_TypeChecker_Env.dsenv);
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
                    FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar =
                      (e.FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar)
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
                    FStar_TypeChecker_Env.tc_term =
                      (e1.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
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
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (e1.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (e1.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (e1.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (e1.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (e1.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (e1.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
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
                    FStar_TypeChecker_Env.unif_allow_ref_guards =
                      (e1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                    FStar_TypeChecker_Env.erase_erasable_args =
                      (e1.FStar_TypeChecker_Env.erase_erasable_args);
                    FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar =
                      (e1.FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar)
                  } in
                try
                  (fun uu___1 ->
                     match () with
                     | () ->
                         let uu___2 = FStar_TypeChecker_TcTerm.tc_term e2 t in
                         FStar_Tactics_Monad.ret uu___2) ()
                with
                | FStar_Errors.Err (uu___2, msg, uu___3) ->
                    let uu___4 = tts e2 t in
                    let uu___5 =
                      let uu___6 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_Compiler_Effect.op_Bar_Greater uu___6
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type (3) %s in context (%s). Error = (%s)"
                      uu___4 uu___5 msg
                | FStar_Errors.Error (uu___2, msg, uu___3, uu___4) ->
                    let uu___5 = tts e2 t in
                    let uu___6 =
                      let uu___7 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_Compiler_Effect.op_Bar_Greater uu___7
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type (3) %s in context (%s). Error = (%s)"
                      uu___5 uu___6 msg))
let (get_guard_policy :
  unit -> FStar_Tactics_Types.guard_policy FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps -> FStar_Tactics_Monad.ret ps.FStar_Tactics_Types.guard_policy)
let (set_guard_policy :
  FStar_Tactics_Types.guard_policy -> unit FStar_Tactics_Monad.tac) =
  fun pol ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_Tactics_Monad.set
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
             FStar_Tactics_Types.guard_policy = pol;
             FStar_Tactics_Types.freshness =
               (ps.FStar_Tactics_Types.freshness);
             FStar_Tactics_Types.tac_verb_dbg =
               (ps.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (ps.FStar_Tactics_Types.local_state);
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
           })
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun pol ->
    fun t ->
      let uu___ = get_guard_policy () in
      FStar_Tactics_Monad.bind uu___
        (fun old_pol ->
           let uu___1 = set_guard_policy pol in
           FStar_Tactics_Monad.bind uu___1
             (fun uu___2 ->
                FStar_Tactics_Monad.bind t
                  (fun r ->
                     let uu___3 = set_guard_policy old_pol in
                     FStar_Tactics_Monad.bind uu___3
                       (fun uu___4 -> FStar_Tactics_Monad.ret r))))
let (proc_guard' :
  Prims.bool ->
    Prims.string ->
      env ->
        FStar_TypeChecker_Common.guard_t ->
          FStar_Compiler_Range.range -> unit FStar_Tactics_Monad.tac)
  =
  fun simplify ->
    fun reason ->
      fun e ->
        fun g ->
          fun rng ->
            FStar_Tactics_Monad.mlog
              (fun uu___ ->
                 let uu___1 = FStar_TypeChecker_Rel.guard_to_string e g in
                 FStar_Compiler_Util.print2 "Processing guard (%s:%s)\n"
                   reason uu___1)
              (fun uu___ ->
                 let uu___1 =
                   FStar_Tactics_Monad.add_implicits
                     g.FStar_TypeChecker_Common.implicits in
                 FStar_Tactics_Monad.bind uu___1
                   (fun uu___2 ->
                      let guard_f =
                        if simplify
                        then
                          let uu___3 =
                            FStar_TypeChecker_Rel.simplify_guard e g in
                          uu___3.FStar_TypeChecker_Common.guard_f
                        else g.FStar_TypeChecker_Common.guard_f in
                      match guard_f with
                      | FStar_TypeChecker_Common.Trivial ->
                          FStar_Tactics_Monad.ret ()
                      | FStar_TypeChecker_Common.NonTrivial f ->
                          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
                            (fun ps ->
                               match ps.FStar_Tactics_Types.guard_policy with
                               | FStar_Tactics_Types.Drop ->
                                   ((let uu___4 =
                                       let uu___5 =
                                         let uu___6 =
                                           FStar_TypeChecker_Rel.guard_to_string
                                             e g in
                                         FStar_Compiler_Util.format1
                                           "Tactics admitted guard <%s>\n\n"
                                           uu___6 in
                                       (FStar_Errors.Warning_TacAdmit,
                                         uu___5) in
                                     FStar_Errors.log_issue
                                       e.FStar_TypeChecker_Env.range uu___4);
                                    FStar_Tactics_Monad.ret ())
                               | FStar_Tactics_Types.Goal ->
                                   FStar_Tactics_Monad.mlog
                                     (fun uu___3 ->
                                        let uu___4 =
                                          FStar_TypeChecker_Rel.guard_to_string
                                            e g in
                                        FStar_Compiler_Util.print2
                                          "Making guard (%s:%s) into a goal\n"
                                          reason uu___4)
                                     (fun uu___3 ->
                                        let uu___4 =
                                          FStar_Tactics_Monad.goal_of_guard
                                            reason e f rng in
                                        FStar_Tactics_Monad.bind uu___4
                                          (fun g1 ->
                                             FStar_Tactics_Monad.push_goals
                                               [g1]))
                               | FStar_Tactics_Types.SMT ->
                                   FStar_Tactics_Monad.mlog
                                     (fun uu___3 ->
                                        let uu___4 =
                                          FStar_TypeChecker_Rel.guard_to_string
                                            e g in
                                        FStar_Compiler_Util.print2
                                          "Sending guard (%s:%s) to SMT goal\n"
                                          reason uu___4)
                                     (fun uu___3 ->
                                        let uu___4 =
                                          FStar_Tactics_Monad.goal_of_guard
                                            reason e f rng in
                                        FStar_Tactics_Monad.bind uu___4
                                          (fun g1 ->
                                             FStar_Tactics_Monad.push_smt_goals
                                               [g1]))
                               | FStar_Tactics_Types.Force ->
                                   FStar_Tactics_Monad.mlog
                                     (fun uu___3 ->
                                        let uu___4 =
                                          FStar_TypeChecker_Rel.guard_to_string
                                            e g in
                                        FStar_Compiler_Util.print2
                                          "Forcing guard (%s:%s)\n" reason
                                          uu___4)
                                     (fun uu___3 ->
                                        try
                                          (fun uu___4 ->
                                             match () with
                                             | () ->
                                                 let uu___5 =
                                                   let uu___6 =
                                                     let uu___7 =
                                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                         e g in
                                                     FStar_Compiler_Effect.op_Less_Bar
                                                       FStar_TypeChecker_Env.is_trivial
                                                       uu___7 in
                                                   Prims.op_Negation uu___6 in
                                                 if uu___5
                                                 then
                                                   FStar_Tactics_Monad.mlog
                                                     (fun uu___6 ->
                                                        let uu___7 =
                                                          FStar_TypeChecker_Rel.guard_to_string
                                                            e g in
                                                        FStar_Compiler_Util.print1
                                                          "guard = %s\n"
                                                          uu___7)
                                                     (fun uu___6 ->
                                                        fail1
                                                          "Forcing the guard failed (%s)"
                                                          reason)
                                                 else
                                                   FStar_Tactics_Monad.ret ())
                                            ()
                                        with
                                        | uu___4 ->
                                            FStar_Tactics_Monad.mlog
                                              (fun uu___5 ->
                                                 let uu___6 =
                                                   FStar_TypeChecker_Rel.guard_to_string
                                                     e g in
                                                 FStar_Compiler_Util.print1
                                                   "guard = %s\n" uu___6)
                                              (fun uu___5 ->
                                                 fail1
                                                   "Forcing the guard failed (%s)"
                                                   reason)))))
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Common.guard_t ->
        FStar_Compiler_Range.range -> unit FStar_Tactics_Monad.tac)
  = proc_guard' true
let (tcc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu___ =
        let uu___1 = __tc_lax e t in
        FStar_Tactics_Monad.bind uu___1
          (fun uu___2 ->
             match uu___2 with
             | (uu___3, lc, uu___4) ->
                 let uu___5 =
                   let uu___6 = FStar_TypeChecker_Common.lcomp_comp lc in
                   FStar_Compiler_Effect.op_Bar_Greater uu___6
                     FStar_Pervasives_Native.fst in
                 FStar_Tactics_Monad.ret uu___5) in
      FStar_Compiler_Effect.op_Less_Bar (FStar_Tactics_Monad.wrap_err "tcc")
        uu___
let (tc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Reflection_Data.typ FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu___ =
        let uu___1 = tcc e t in
        FStar_Tactics_Monad.bind uu___1
          (fun c -> FStar_Tactics_Monad.ret (FStar_Syntax_Util.comp_result c)) in
      FStar_Compiler_Effect.op_Less_Bar (FStar_Tactics_Monad.wrap_err "tc")
        uu___
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
             let uu___ =
               try
                 (fun uu___1 ->
                    match () with
                    | () ->
                        let uu___2 =
                          let uu___3 = FStar_BigInt.to_int_fs n in
                          FStar_Compiler_List.splitAt uu___3
                            p.FStar_Tactics_Types.goals in
                        FStar_Tactics_Monad.ret uu___2) ()
               with
               | uu___1 ->
                   FStar_Tactics_Monad.fail "divide: not enough goals" in
             FStar_Tactics_Monad.bind uu___
               (fun uu___1 ->
                  match uu___1 with
                  | (lgs, rgs) ->
                      let lp =
                        {
                          FStar_Tactics_Types.main_context =
                            (p.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (p.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (p.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (p.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (p.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (p.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (p.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (p.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (p.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (p.FStar_Tactics_Types.local_state);
                          FStar_Tactics_Types.urgency =
                            (p.FStar_Tactics_Types.urgency)
                        } in
                      let uu___2 = FStar_Tactics_Monad.set lp in
                      FStar_Tactics_Monad.bind uu___2
                        (fun uu___3 ->
                           FStar_Tactics_Monad.bind l
                             (fun a1 ->
                                FStar_Tactics_Monad.bind
                                  FStar_Tactics_Monad.get
                                  (fun lp' ->
                                     let rp =
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (lp'.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (lp'.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (lp'.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (lp'.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (lp'.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (lp'.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (lp'.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (lp'.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (lp'.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (lp'.FStar_Tactics_Types.local_state);
                                         FStar_Tactics_Types.urgency =
                                           (lp'.FStar_Tactics_Types.urgency)
                                       } in
                                     let uu___4 = FStar_Tactics_Monad.set rp in
                                     FStar_Tactics_Monad.bind uu___4
                                       (fun uu___5 ->
                                          FStar_Tactics_Monad.bind r
                                            (fun b1 ->
                                               FStar_Tactics_Monad.bind
                                                 FStar_Tactics_Monad.get
                                                 (fun rp' ->
                                                    let p' =
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (rp'.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (rp'.FStar_Tactics_Types.all_implicits);
                                                        FStar_Tactics_Types.goals
                                                          =
                                                          (FStar_Compiler_List.op_At
                                                             lp'.FStar_Tactics_Types.goals
                                                             rp'.FStar_Tactics_Types.goals);
                                                        FStar_Tactics_Types.smt_goals
                                                          =
                                                          (FStar_Compiler_List.op_At
                                                             lp'.FStar_Tactics_Types.smt_goals
                                                             (FStar_Compiler_List.op_At
                                                                rp'.FStar_Tactics_Types.smt_goals
                                                                p.FStar_Tactics_Types.smt_goals));
                                                        FStar_Tactics_Types.depth
                                                          =
                                                          (rp'.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (rp'.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (rp'.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (rp'.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (rp'.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (rp'.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (rp'.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (rp'.FStar_Tactics_Types.local_state);
                                                        FStar_Tactics_Types.urgency
                                                          =
                                                          (rp'.FStar_Tactics_Types.urgency)
                                                      } in
                                                    let uu___6 =
                                                      FStar_Tactics_Monad.set
                                                        p' in
                                                    FStar_Tactics_Monad.bind
                                                      uu___6
                                                      (fun uu___7 ->
                                                         FStar_Tactics_Monad.bind
                                                           FStar_Tactics_Monad.remove_solved_goals
                                                           (fun uu___8 ->
                                                              FStar_Tactics_Monad.ret
                                                                (a1, b1)))))))))))
let focus : 'a . 'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac =
  fun f ->
    let uu___ = divide FStar_BigInt.one f FStar_Tactics_Monad.idtac in
    FStar_Tactics_Monad.bind uu___
      (fun uu___1 ->
         match uu___1 with | (a1, ()) -> FStar_Tactics_Monad.ret a1)
let rec map :
  'a . 'a FStar_Tactics_Monad.tac -> 'a Prims.list FStar_Tactics_Monad.tac =
  fun tau ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun p ->
         match p.FStar_Tactics_Types.goals with
         | [] -> FStar_Tactics_Monad.ret []
         | uu___::uu___1 ->
             let uu___2 =
               let uu___3 = map tau in divide FStar_BigInt.one tau uu___3 in
             FStar_Tactics_Monad.bind uu___2
               (fun uu___3 ->
                  match uu___3 with
                  | (h, t) -> FStar_Tactics_Monad.ret (h :: t)))
let (seq :
  unit FStar_Tactics_Monad.tac ->
    unit FStar_Tactics_Monad.tac -> unit FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let uu___ =
        FStar_Tactics_Monad.bind t1
          (fun uu___1 ->
             let uu___2 = map t2 in
             FStar_Tactics_Monad.bind uu___2
               (fun uu___3 -> FStar_Tactics_Monad.ret ())) in
      focus uu___
let (should_check_goal_uvar :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.should_check_uvar) =
  fun g ->
    FStar_Syntax_Util.ctx_uvar_should_check
      g.FStar_Tactics_Types.goal_ctx_uvar
let (bnorm_and_replace :
  FStar_Tactics_Types.goal -> unit FStar_Tactics_Monad.tac) =
  fun g -> let uu___ = bnorm_goal g in FStar_Tactics_Monad.replace_cur uu___
let (intro : unit -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu___2 =
             let uu___3 =
               let uu___4 = FStar_Tactics_Types.goal_env goal in
               let uu___5 = FStar_Tactics_Types.goal_type goal in
               whnf uu___4 uu___5 in
             FStar_Syntax_Util.arrow_one uu___3 in
           match uu___2 with
           | FStar_Pervasives_Native.Some (b, c) ->
               let uu___3 =
                 let uu___4 = FStar_Syntax_Util.is_total_comp c in
                 Prims.op_Negation uu___4 in
               if uu___3
               then FStar_Tactics_Monad.fail "Codomain is effectful"
               else
                 (let env' =
                    let uu___5 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.push_binders uu___5 [b] in
                  let typ' = FStar_Syntax_Util.comp_result c in
                  let uu___5 =
                    let uu___6 =
                      let uu___7 = should_check_goal_uvar goal in
                      FStar_Pervasives_Native.Some uu___7 in
                    FStar_Tactics_Monad.new_uvar "intro" env' typ' uu___6
                      (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_apply_tac_prefix
                      (rangeof goal) in
                  FStar_Tactics_Monad.bind uu___5
                    (fun uu___6 ->
                       match uu___6 with
                       | (body, ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)) in
                           let uu___7 = set_solution goal sol in
                           FStar_Tactics_Monad.bind uu___7
                             (fun uu___8 ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label in
                                let uu___9 = bnorm_and_replace g in
                                FStar_Tactics_Monad.bind uu___9
                                  (fun uu___10 -> FStar_Tactics_Monad.ret b))))
           | FStar_Pervasives_Native.None ->
               let uu___3 =
                 let uu___4 = FStar_Tactics_Types.goal_env goal in
                 let uu___5 = FStar_Tactics_Types.goal_type goal in
                 tts uu___4 uu___5 in
               fail1 "goal is not an arrow (%s)" uu___3) in
    FStar_Compiler_Effect.op_Less_Bar (FStar_Tactics_Monad.wrap_err "intro")
      uu___1
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder)
      FStar_Tactics_Monad.tac)
  =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Compiler_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Compiler_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu___3 =
            let uu___4 =
              let uu___5 = FStar_Tactics_Types.goal_env goal in
              let uu___6 = FStar_Tactics_Types.goal_type goal in
              whnf uu___5 uu___6 in
            FStar_Syntax_Util.arrow_one uu___4 in
          match uu___3 with
          | FStar_Pervasives_Native.Some (b, c) ->
              let uu___4 =
                let uu___5 = FStar_Syntax_Util.is_total_comp c in
                Prims.op_Negation uu___5 in
              if uu___4
              then FStar_Tactics_Monad.fail "Codomain is effectful"
              else
                (let bv =
                   let uu___6 = FStar_Tactics_Types.goal_type goal in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu___6 in
                 let bs =
                   let uu___6 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu___6; b] in
                 let env' =
                   let uu___6 = FStar_Tactics_Types.goal_env goal in
                   FStar_TypeChecker_Env.push_binders uu___6 bs in
                 let uu___6 =
                   let uu___7 =
                     let uu___8 = should_check_goal_uvar goal in
                     FStar_Pervasives_Native.Some uu___8 in
                   FStar_Tactics_Monad.new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c) uu___7
                     (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_apply_tac_prefix
                     (rangeof goal) in
                 FStar_Tactics_Monad.bind uu___6
                   (fun uu___7 ->
                      match uu___7 with
                      | (u, ctx_uvar_u) ->
                          let lb =
                            let uu___8 = FStar_Tactics_Types.goal_type goal in
                            let uu___9 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Pervasives.Inl bv) [] uu___8
                              FStar_Parser_Const.effect_Tot_lid uu___9 []
                              FStar_Compiler_Range.dummyRange in
                          let body = FStar_Syntax_Syntax.bv_to_name bv in
                          let uu___8 =
                            FStar_Syntax_Subst.close_let_rec [lb] body in
                          (match uu___8 with
                           | (lbs, body1) ->
                               let tm =
                                 let uu___9 =
                                   let uu___10 =
                                     FStar_Tactics_Types.goal_witness goal in
                                   uu___10.FStar_Syntax_Syntax.pos in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1)) uu___9 in
                               let uu___9 = set_solution goal tm in
                               FStar_Tactics_Monad.bind uu___9
                                 (fun uu___10 ->
                                    let uu___11 =
                                      bnorm_and_replace
                                        {
                                          FStar_Tactics_Types.goal_main_env =
                                            (goal.FStar_Tactics_Types.goal_main_env);
                                          FStar_Tactics_Types.goal_ctx_uvar =
                                            ctx_uvar_u;
                                          FStar_Tactics_Types.opts =
                                            (goal.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (goal.FStar_Tactics_Types.is_guard);
                                          FStar_Tactics_Types.label =
                                            (goal.FStar_Tactics_Types.label)
                                        } in
                                    FStar_Tactics_Monad.bind uu___11
                                      (fun uu___12 ->
                                         let uu___13 =
                                           let uu___14 =
                                             FStar_Syntax_Syntax.mk_binder bv in
                                           (uu___14, b) in
                                         FStar_Tactics_Monad.ret uu___13)))))
          | FStar_Pervasives_Native.None ->
              let uu___4 =
                let uu___5 = FStar_Tactics_Types.goal_env goal in
                let uu___6 = FStar_Tactics_Types.goal_type goal in
                tts uu___5 uu___6 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu___4))
let (norm :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu___ ->
              let uu___1 =
                let uu___2 = FStar_Tactics_Types.goal_witness goal in
                FStar_Syntax_Print.term_to_string uu___2 in
              FStar_Compiler_Util.print1 "norm: witness = %s\n" uu___1)
           (fun uu___ ->
              let steps =
                let uu___1 = FStar_TypeChecker_Cfg.translate_norm_steps s in
                FStar_Compiler_List.op_At
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu___1 in
              let t =
                let uu___1 = FStar_Tactics_Types.goal_env goal in
                let uu___2 = FStar_Tactics_Types.goal_type goal in
                normalize steps uu___1 uu___2 in
              let uu___1 = goal_with_type goal t in
              FStar_Tactics_Monad.replace_cur uu___1))
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun s ->
      fun t ->
        let uu___ =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu___1 -> g.FStar_Tactics_Types.opts
                 | uu___1 -> FStar_Options.peek () in
               FStar_Tactics_Monad.mlog
                 (fun uu___1 ->
                    let uu___2 = FStar_Syntax_Print.term_to_string t in
                    FStar_Compiler_Util.print1 "norm_term_env: t = %s\n"
                      uu___2)
                 (fun uu___1 ->
                    let uu___2 = __tc_lax e t in
                    FStar_Tactics_Monad.bind uu___2
                      (fun uu___3 ->
                         match uu___3 with
                         | (t1, uu___4, uu___5) ->
                             let steps =
                               let uu___6 =
                                 FStar_TypeChecker_Cfg.translate_norm_steps s in
                               FStar_Compiler_List.op_At
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu___6 in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1 in
                             FStar_Tactics_Monad.mlog
                               (fun uu___6 ->
                                  let uu___7 =
                                    FStar_Syntax_Print.term_to_string t2 in
                                  FStar_Compiler_Util.print1
                                    "norm_term_env: t' = %s\n" uu___7)
                               (fun uu___6 -> FStar_Tactics_Monad.ret t2)))) in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "norm_term") uu___
let (refine_intro : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu___2 =
             let uu___3 = FStar_Tactics_Types.goal_env g in
             let uu___4 = FStar_Tactics_Types.goal_type g in
             FStar_TypeChecker_Rel.base_and_refinement uu___3 uu___4 in
           match uu___2 with
           | (uu___3, FStar_Pervasives_Native.None) ->
               FStar_Tactics_Monad.fail "not a refinement"
           | (t, FStar_Pervasives_Native.Some (bv, phi)) ->
               (mark_goal_implicit_allow_untyped g;
                (let g1 = goal_with_type g t in
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
                       FStar_Tactics_Monad.mk_irrelevant_goal
                         "refine_intro refinement" uu___6 uu___7 (rangeof g)
                         g.FStar_Tactics_Types.opts
                         g.FStar_Tactics_Types.label in
                     FStar_Tactics_Monad.bind uu___5
                       (fun g2 ->
                          FStar_Tactics_Monad.bind
                            FStar_Tactics_Monad.dismiss
                            (fun uu___6 ->
                               FStar_Tactics_Monad.add_goals [g1; g2]))))) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "refine_intro") uu___1
let (__exact_now :
  Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun set_expected_typ ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let env1 =
             if set_expected_typ
             then
               let uu___ = FStar_Tactics_Types.goal_env goal in
               let uu___1 = FStar_Tactics_Types.goal_type goal in
               FStar_TypeChecker_Env.set_expected_typ uu___ uu___1
             else FStar_Tactics_Types.goal_env goal in
           let uu___ = __tc env1 t in
           FStar_Tactics_Monad.bind uu___
             (fun uu___1 ->
                match uu___1 with
                | (t1, typ, guard) ->
                    FStar_Tactics_Monad.mlog
                      (fun uu___2 ->
                         let uu___3 = FStar_Syntax_Print.term_to_string typ in
                         let uu___4 =
                           let uu___5 = FStar_Tactics_Types.goal_env goal in
                           FStar_TypeChecker_Rel.guard_to_string uu___5 guard in
                         FStar_Compiler_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu___3 uu___4)
                      (fun uu___2 ->
                         let uu___3 =
                           let uu___4 = FStar_Tactics_Types.goal_env goal in
                           proc_guard "__exact typing" uu___4 guard
                             (rangeof goal) in
                         FStar_Tactics_Monad.bind uu___3
                           (fun uu___4 ->
                              FStar_Tactics_Monad.mlog
                                (fun uu___5 ->
                                   let uu___6 =
                                     FStar_Syntax_Print.term_to_string typ in
                                   let uu___7 =
                                     let uu___8 =
                                       FStar_Tactics_Types.goal_type goal in
                                     FStar_Syntax_Print.term_to_string uu___8 in
                                   FStar_Compiler_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu___6 uu___7)
                                (fun uu___5 ->
                                   let uu___6 =
                                     let uu___7 =
                                       FStar_Tactics_Types.goal_env goal in
                                     let uu___8 =
                                       FStar_Tactics_Types.goal_type goal in
                                     do_unify uu___7 typ uu___8 in
                                   FStar_Tactics_Monad.bind uu___6
                                     (fun b ->
                                        if b
                                        then
                                          (mark_goal_implicit_allow_untyped
                                             goal;
                                           solve goal t1)
                                        else
                                          (let uu___8 =
                                             let uu___9 =
                                               let uu___10 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal in
                                               tts uu___10 in
                                             let uu___10 =
                                               FStar_Tactics_Types.goal_type
                                                 goal in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu___9 typ uu___10 in
                                           match uu___8 with
                                           | (typ1, goalt) ->
                                               let uu___9 =
                                                 let uu___10 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 tts uu___10 t1 in
                                               let uu___10 =
                                                 let uu___11 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 let uu___12 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal in
                                                 tts uu___11 uu___12 in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu___9 typ1 goalt uu___10)))))))
let (t_exact :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun try_refine ->
    fun set_expected_typ ->
      fun tm ->
        let uu___ =
          FStar_Tactics_Monad.mlog
            (fun uu___1 ->
               let uu___2 = FStar_Syntax_Print.term_to_string tm in
               FStar_Compiler_Util.print1 "t_exact: tm = %s\n" uu___2)
            (fun uu___1 ->
               let uu___2 =
                 let uu___3 = __exact_now set_expected_typ tm in
                 FStar_Tactics_Monad.catch uu___3 in
               FStar_Tactics_Monad.bind uu___2
                 (fun uu___3 ->
                    match uu___3 with
                    | FStar_Pervasives.Inr r -> FStar_Tactics_Monad.ret ()
                    | FStar_Pervasives.Inl e when
                        Prims.op_Negation try_refine ->
                        FStar_Tactics_Monad.traise e
                    | FStar_Pervasives.Inl e ->
                        FStar_Tactics_Monad.mlog
                          (fun uu___4 ->
                             FStar_Compiler_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu___4 ->
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   norm [FStar_Syntax_Embeddings.Delta] in
                                 FStar_Tactics_Monad.bind uu___7
                                   (fun uu___8 ->
                                      let uu___9 = refine_intro () in
                                      FStar_Tactics_Monad.bind uu___9
                                        (fun uu___10 ->
                                           __exact_now set_expected_typ tm)) in
                               FStar_Tactics_Monad.catch uu___6 in
                             FStar_Tactics_Monad.bind uu___5
                               (fun uu___6 ->
                                  match uu___6 with
                                  | FStar_Pervasives.Inr r ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu___7 ->
                                           FStar_Compiler_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu___7 ->
                                           FStar_Tactics_Monad.ret ())
                                  | FStar_Pervasives.Inl uu___7 ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu___8 ->
                                           FStar_Compiler_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu___8 ->
                                           FStar_Tactics_Monad.traise e))))) in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "exact") uu___
let rec (__try_unify_by_application :
  Prims.bool ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.ctx_uvar Prims.list ->
              FStar_Compiler_Range.range ->
                (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
                  FStar_Syntax_Syntax.ctx_uvar) Prims.list
                  FStar_Tactics_Monad.tac)
  =
  fun only_match ->
    fun acc ->
      fun e ->
        fun ty1 ->
          fun ty2 ->
            fun ty2_uvars ->
              fun rng ->
                let f = if only_match then do_match else do_unify in
                let uu___ = f e ty2 ty1 in
                FStar_Tactics_Monad.bind uu___
                  (fun uu___1 ->
                     if uu___1
                     then
                       (FStar_Compiler_Effect.op_Bar_Greater ty2_uvars
                          (FStar_Compiler_List.iter
                             (fun u ->
                                let uu___3 =
                                  FStar_Syntax_Unionfind.find
                                    u.FStar_Syntax_Syntax.ctx_uvar_head in
                                match uu___3 with
                                | FStar_Pervasives_Native.None -> ()
                                | FStar_Pervasives_Native.Some sol ->
                                    let uu___4 =
                                      let uu___5 =
                                        FStar_Syntax_Util.ctx_uvar_typ u in
                                      core_check e
                                        u.FStar_Syntax_Syntax.ctx_uvar_gamma
                                        sol uu___5 in
                                    (match uu___4 with
                                     | FStar_Pervasives.Inl
                                         (FStar_Pervasives_Native.None) ->
                                         mark_uvar_as_allow_untyped u
                                     | uu___5 -> ())));
                        FStar_Tactics_Monad.ret acc)
                     else
                       (let uu___2 = FStar_Syntax_Util.arrow_one ty1 in
                        match uu___2 with
                        | FStar_Pervasives_Native.None ->
                            let uu___3 = term_to_string e ty1 in
                            let uu___4 = term_to_string e ty2 in
                            fail2 "Could not instantiate, %s to %s" uu___3
                              uu___4
                        | FStar_Pervasives_Native.Some (b, c) ->
                            let uu___3 =
                              let uu___4 = FStar_Syntax_Util.is_total_comp c in
                              Prims.op_Negation uu___4 in
                            if uu___3
                            then
                              FStar_Tactics_Monad.fail
                                "Codomain is effectful"
                            else
                              (let uvar_deps =
                                 let bv_sort_free_uvs =
                                   FStar_Syntax_Free.uvars
                                     (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                 let uu___5 =
                                   FStar_Compiler_Effect.op_Bar_Greater acc
                                     (FStar_Compiler_List.filter
                                        (fun uu___6 ->
                                           match uu___6 with
                                           | (uu___7, uu___8, uv) ->
                                               FStar_Compiler_Util.set_mem uv
                                                 bv_sort_free_uvs)) in
                                 FStar_Compiler_Effect.op_Bar_Greater uu___5
                                   (FStar_Compiler_List.map
                                      (fun uu___6 ->
                                         match uu___6 with
                                         | (uu___7, uu___8, uv) -> uv)) in
                               let uu___5 =
                                 FStar_Tactics_Monad.new_uvar "apply arg" e
                                   (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                   FStar_Pervasives_Native.None uvar_deps rng in
                               FStar_Tactics_Monad.bind uu___5
                                 (fun uu___6 ->
                                    match uu___6 with
                                    | (uvt, uv) ->
                                        FStar_Tactics_Monad.mlog
                                          (fun uu___7 ->
                                             let uu___8 =
                                               FStar_Syntax_Print.ctx_uvar_to_string
                                                 uv in
                                             FStar_Compiler_Util.print1
                                               "t_apply: generated uvar %s\n"
                                               uu___8)
                                          (fun uu___7 ->
                                             let typ =
                                               FStar_Syntax_Util.comp_result
                                                 c in
                                             let typ' =
                                               FStar_Syntax_Subst.subst
                                                 [FStar_Syntax_Syntax.NT
                                                    ((b.FStar_Syntax_Syntax.binder_bv),
                                                      uvt)] typ in
                                             let uu___8 =
                                               let uu___9 =
                                                 let uu___10 =
                                                   FStar_Syntax_Util.aqual_of_binder
                                                     b in
                                                 (uvt, uu___10, uv) in
                                               uu___9 :: acc in
                                             __try_unify_by_application
                                               only_match uu___8 e typ' ty2
                                               ty2_uvars rng)))))
let (try_unify_by_application :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Compiler_Range.range ->
            (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
              FStar_Syntax_Syntax.ctx_uvar) Prims.list
              FStar_Tactics_Monad.tac)
  =
  fun only_match ->
    fun e ->
      fun ty1 ->
        fun ty2 ->
          fun rng ->
            let ty2_uvars = FStar_Syntax_Free.uvars ty2 in
            let uu___ = FStar_Compiler_Util.set_elements ty2_uvars in
            __try_unify_by_application only_match [] e ty1 ty2 uu___ rng
let (check_apply_implicits_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Tactics_Types.goal FStar_Pervasives_Native.option ->
        Prims.bool ->
          Prims.string ->
            Prims.bool ->
              (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar)
                Prims.list ->
                FStar_Tactics_Types.goal Prims.list Prims.list
                  FStar_Tactics_Monad.tac)
  =
  fun simplify_guard ->
    fun env1 ->
      fun gl ->
        fun debug_on ->
          fun debug_prefix ->
            fun must_tot ->
              fun imps ->
                let check_implicits_solution env2 gamma t k must_tot1 =
                  let uu___ = core_check env2 gamma t k in
                  let env3 =
                    FStar_TypeChecker_Env.set_expected_typ
                      {
                        FStar_TypeChecker_Env.solver =
                          (env2.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (env2.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (env2.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (env2.FStar_TypeChecker_Env.gamma);
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
                        FStar_TypeChecker_Env.instantiate_imp =
                          (env2.FStar_TypeChecker_Env.instantiate_imp);
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
                        FStar_TypeChecker_Env.admit =
                          (env2.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (env2.FStar_TypeChecker_Env.lax);
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
                        FStar_TypeChecker_Env.tc_term =
                          (env2.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                          (env2.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                        FStar_TypeChecker_Env.universe_of =
                          (env2.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                          =
                          (env2.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                        FStar_TypeChecker_Env.teq_nosmt_force =
                          (env2.FStar_TypeChecker_Env.teq_nosmt_force);
                        FStar_TypeChecker_Env.subtype_nosmt_force =
                          (env2.FStar_TypeChecker_Env.subtype_nosmt_force);
                        FStar_TypeChecker_Env.use_bv_sorts = true;
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
                        FStar_TypeChecker_Env.dsenv =
                          (env2.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (env2.FStar_TypeChecker_Env.nbe);
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
                        FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar =
                          (env2.FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar)
                      } k in
                  let slow_path uu___1 =
                    let uu___2 =
                      FStar_TypeChecker_TcTerm.typeof_tot_or_gtot_term env3 t
                        must_tot1 in
                    match uu___2 with | (uu___3, uu___4, g) -> g in
                  let uu___1 =
                    FStar_TypeChecker_TcTerm.typeof_tot_or_gtot_term_fastpath
                      env3 t must_tot1 in
                  match uu___1 with
                  | FStar_Pervasives_Native.None -> slow_path ()
                  | FStar_Pervasives_Native.Some k' ->
                      let uu___2 =
                        FStar_TypeChecker_Rel.subtype_nosmt env3 k' k in
                      (match uu___2 with
                       | FStar_Pervasives_Native.None -> slow_path ()
                       | FStar_Pervasives_Native.Some g -> g) in
                let check_one_implicit uu___ =
                  match uu___ with
                  | (term, ctx_uvar) ->
                      let uu___1 = FStar_Syntax_Util.head_and_args term in
                      (match uu___1 with
                       | (hd, uu___2) ->
                           let uu___3 =
                             let uu___4 = FStar_Syntax_Subst.compress hd in
                             uu___4.FStar_Syntax_Syntax.n in
                           (match uu___3 with
                            | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar1, uu___4)
                                ->
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
                                FStar_Tactics_Monad.ret [gl2]
                            | uu___4 ->
                                FStar_Tactics_Monad.mlog
                                  (fun uu___5 ->
                                     let uu___6 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                                     let uu___7 =
                                       FStar_Syntax_Print.term_to_string term in
                                     FStar_Compiler_Util.print3
                                       "%s: arg %s unified to (%s)\n"
                                       debug_prefix uu___6 uu___7)
                                  (fun uu___5 ->
                                     let g_typ =
                                       let uu___6 =
                                         FStar_Syntax_Util.ctx_uvar_typ
                                           ctx_uvar in
                                       check_implicits_solution env1
                                         ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma
                                         term uu___6 must_tot in
                                     let rng =
                                       match gl with
                                       | FStar_Pervasives_Native.None ->
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_range
                                       | FStar_Pervasives_Native.Some gl1 ->
                                           rangeof gl1 in
                                     let uu___6 =
                                       let uu___7 =
                                         if debug_on
                                         then
                                           let uu___8 =
                                             FStar_Syntax_Print.ctx_uvar_to_string
                                               ctx_uvar in
                                           let uu___9 =
                                             FStar_Syntax_Print.term_to_string
                                               term in
                                           FStar_Compiler_Util.format3
                                             "%s solved arg %s to %s\n"
                                             debug_prefix uu___8 uu___9
                                         else
                                           FStar_Compiler_Util.format1
                                             "%s solved arg" debug_prefix in
                                       proc_guard' simplify_guard uu___7 env1
                                         g_typ rng in
                                     FStar_Tactics_Monad.bind uu___6
                                       (fun uu___7 ->
                                          mark_uvar_as_allow_untyped ctx_uvar;
                                          FStar_Tactics_Monad.ret [])))) in
                FStar_Compiler_Effect.op_Bar_Greater imps
                  (FStar_Tactics_Monad.mapM check_one_implicit)
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
            FStar_Tactics_Monad.mlog
              (fun uu___1 ->
                 let uu___2 = FStar_Compiler_Util.string_of_bool uopt in
                 let uu___3 = FStar_Compiler_Util.string_of_bool only_match in
                 let uu___4 =
                   FStar_Compiler_Util.string_of_bool tc_resolved_uvars in
                 let uu___5 = FStar_Syntax_Print.term_to_string tm in
                 FStar_Compiler_Util.print4
                   "t_apply: uopt %s, only_match %s, tc_resolved_uvars %s, tm = %s\n"
                   uu___2 uu___3 uu___4 uu___5)
              (fun uu___1 ->
                 FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
                   (fun ps ->
                      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                        (fun goal ->
                           let e = FStar_Tactics_Types.goal_env goal in
                           FStar_Tactics_Monad.mlog
                             (fun uu___2 ->
                                let uu___3 =
                                  FStar_Syntax_Print.term_to_string tm in
                                let uu___4 =
                                  FStar_Tactics_Printing.goal_to_string_verbose
                                    goal in
                                let uu___5 =
                                  FStar_TypeChecker_Env.print_gamma
                                    e.FStar_TypeChecker_Env.gamma in
                                FStar_Compiler_Util.print3
                                  "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\n"
                                  uu___3 uu___4 uu___5)
                             (fun uu___2 ->
                                let uu___3 = __tc e tm in
                                FStar_Tactics_Monad.bind uu___3
                                  (fun uu___4 ->
                                     match uu___4 with
                                     | (tm1, typ, guard) ->
                                         let typ1 = bnorm e typ in
                                         let uu___5 =
                                           let uu___6 =
                                             FStar_Tactics_Types.goal_type
                                               goal in
                                           try_unify_by_application
                                             only_match e typ1 uu___6
                                             (rangeof goal) in
                                         FStar_Tactics_Monad.bind uu___5
                                           (fun uvs ->
                                              FStar_Tactics_Monad.mlog
                                                (fun uu___6 ->
                                                   let uu___7 =
                                                     FStar_Common.string_of_list
                                                       (fun uu___8 ->
                                                          match uu___8 with
                                                          | (t, uu___9,
                                                             uu___10) ->
                                                              FStar_Syntax_Print.term_to_string
                                                                t) uvs in
                                                   FStar_Compiler_Util.print1
                                                     "t_apply: found args = %s\n"
                                                     uu___7)
                                                (fun uu___6 ->
                                                   let w =
                                                     FStar_Compiler_List.fold_right
                                                       (fun uu___7 ->
                                                          fun w1 ->
                                                            match uu___7 with
                                                            | (uvt, q,
                                                               uu___8) ->
                                                                FStar_Syntax_Util.mk_app
                                                                  w1
                                                                  [(uvt, q)])
                                                       uvs tm1 in
                                                   let uvset =
                                                     let uu___7 =
                                                       FStar_Syntax_Free.new_uv_set
                                                         () in
                                                     FStar_Compiler_List.fold_right
                                                       (fun uu___8 ->
                                                          fun s ->
                                                            match uu___8 with
                                                            | (uu___9,
                                                               uu___10, uv)
                                                                ->
                                                                let uu___11 =
                                                                  let uu___12
                                                                    =
                                                                    FStar_Syntax_Util.ctx_uvar_typ
                                                                    uv in
                                                                  FStar_Syntax_Free.uvars
                                                                    uu___12 in
                                                                FStar_Compiler_Util.set_union
                                                                  s uu___11)
                                                       uvs uu___7 in
                                                   let free_in_some_goal uv =
                                                     FStar_Compiler_Util.set_mem
                                                       uv uvset in
                                                   let uu___7 = solve' goal w in
                                                   FStar_Tactics_Monad.bind
                                                     uu___7
                                                     (fun uu___8 ->
                                                        let uu___9 =
                                                          let uu___10 =
                                                            FStar_Compiler_Effect.op_Bar_Greater
                                                              uvs
                                                              (FStar_Compiler_List.map
                                                                 (fun uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (uvt, _q,
                                                                    uv) ->
                                                                    (uvt, uv))) in
                                                          FStar_Compiler_Effect.op_Bar_Greater
                                                            uu___10
                                                            (if
                                                               tc_resolved_uvars
                                                             then
                                                               let must_tot =
                                                                 true in
                                                               check_apply_implicits_solutions
                                                                 true e
                                                                 (FStar_Pervasives_Native.Some
                                                                    goal)
                                                                 ps.FStar_Tactics_Types.tac_verb_dbg
                                                                 "apply"
                                                                 must_tot
                                                             else
                                                               (fun l ->
                                                                  let uu___12
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    l
                                                                    (FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    (uu___14,
                                                                    uv) ->
                                                                    let uu___15
                                                                    =
                                                                    FStar_Syntax_Unionfind.find
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head in
                                                                    (match uu___15
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___16
                                                                    -> []
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    [
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (goal.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (goal.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (goal.FStar_Tactics_Types.label)
                                                                    }]))) in
                                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___12
                                                                    FStar_Tactics_Monad.ret)) in
                                                        FStar_Tactics_Monad.bind
                                                          uu___9
                                                          (fun subgoals ->
                                                             let uu___10 =
                                                               let uu___11 =
                                                                 let uu___12
                                                                   =
                                                                   let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    subgoals
                                                                    FStar_Compiler_List.flatten in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___14
                                                                    (FStar_Compiler_List.filter
                                                                    (fun g ->
                                                                    let uu___15
                                                                    =
                                                                    uopt &&
                                                                    (free_in_some_goal
                                                                    g.FStar_Tactics_Types.goal_ctx_uvar) in
                                                                    Prims.op_Negation
                                                                    uu___15)) in
                                                                   FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___13
                                                                    (FStar_Compiler_List.map
                                                                    bnorm_goal) in
                                                                 FStar_Compiler_Effect.op_Bar_Greater
                                                                   uu___12
                                                                   FStar_Compiler_List.rev in
                                                               FStar_Compiler_Effect.op_Bar_Greater
                                                                 uu___11
                                                                 FStar_Tactics_Monad.add_goals in
                                                             FStar_Tactics_Monad.bind
                                                               uu___10
                                                               (fun uu___11
                                                                  ->
                                                                  proc_guard
                                                                    "apply guard"
                                                                    e guard
                                                                    (
                                                                    rangeof
                                                                    goal))))))))))) in
          FStar_Compiler_Effect.op_Less_Bar
            (FStar_Tactics_Monad.wrap_err "apply") uu___
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c in
    let uu___ =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid in
    if uu___
    then
      let uu___1 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu___2 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu___2 -> failwith "apply_lemma: impossible: not a lemma" in
      match uu___1 with
      | (pre, post) ->
          let post1 =
            let uu___2 =
              let uu___3 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
              [uu___3] in
            FStar_Syntax_Util.mk_app post uu___2 in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu___2 =
         (FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)
           ||
           (FStar_Syntax_Util.is_ghost_effect
              ct.FStar_Syntax_Syntax.effect_name) in
       if uu___2
       then
         let uu___3 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ in
         FStar_Compiler_Util.map_opt uu___3
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
            let uu___ = f x e in
            FStar_Tactics_Monad.bind uu___ (fun e' -> fold_left f e' xs1)
let (t_apply_lemma :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun noinst ->
    fun noinst_lhs ->
      fun tm ->
        let uu___ =
          let uu___1 =
            FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
              (fun ps ->
                 FStar_Tactics_Monad.mlog
                   (fun uu___2 ->
                      let uu___3 = FStar_Syntax_Print.term_to_string tm in
                      FStar_Compiler_Util.print1 "apply_lemma: tm = %s\n"
                        uu___3)
                   (fun uu___2 ->
                      let is_unit_t t =
                        let uu___3 =
                          let uu___4 = FStar_Syntax_Subst.compress t in
                          uu___4.FStar_Syntax_Syntax.n in
                        match uu___3 with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.unit_lid
                            -> true
                        | uu___4 -> false in
                      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                        (fun goal ->
                           let env1 = FStar_Tactics_Types.goal_env goal in
                           let uu___3 = __tc env1 tm in
                           FStar_Tactics_Monad.bind uu___3
                             (fun uu___4 ->
                                match uu___4 with
                                | (tm1, t, guard) ->
                                    let uu___5 =
                                      FStar_Syntax_Util.arrow_formals_comp t in
                                    (match uu___5 with
                                     | (bs, comp) ->
                                         let uu___6 = lemma_or_sq comp in
                                         (match uu___6 with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Tactics_Monad.fail
                                                "not a lemma or squashed function"
                                          | FStar_Pervasives_Native.Some
                                              (pre, post) ->
                                              let uu___7 =
                                                let tm_uses_subtyping =
                                                  let uu___8 =
                                                    FStar_Syntax_Util.head_and_args
                                                      tm1 in
                                                  match uu___8 with
                                                  | (tm_head, uu___9) ->
                                                      let uu___10 =
                                                        let uu___11 =
                                                          let uu___12 =
                                                            let uu___13 =
                                                              FStar_Compiler_Effect.op_Bar_Greater
                                                                tm_head
                                                                FStar_Syntax_Subst.compress in
                                                            FStar_Compiler_Effect.op_Bar_Greater
                                                              uu___13
                                                              FStar_Syntax_Util.unascribe in
                                                          FStar_Compiler_Effect.op_Bar_Greater
                                                            uu___12
                                                            FStar_Syntax_Util.un_uinst in
                                                        uu___11.FStar_Syntax_Syntax.n in
                                                      (match uu___10 with
                                                       | FStar_Syntax_Syntax.Tm_fvar
                                                           fv ->
                                                           let uu___11 =
                                                             FStar_TypeChecker_Env.fv_has_attr
                                                               env1 fv
                                                               FStar_Parser_Const.no_subtping_attr_lid in
                                                           Prims.op_Negation
                                                             uu___11
                                                       | uu___11 -> true) in
                                                fold_left
                                                  (fun uu___8 ->
                                                     fun uu___9 ->
                                                       match (uu___8, uu___9)
                                                       with
                                                       | ({
                                                            FStar_Syntax_Syntax.binder_bv
                                                              = b;
                                                            FStar_Syntax_Syntax.binder_qual
                                                              = aq;
                                                            FStar_Syntax_Syntax.binder_attrs
                                                              = uu___10;_},
                                                          (uvs, imps, subst))
                                                           ->
                                                           let b_t =
                                                             FStar_Syntax_Subst.subst
                                                               subst
                                                               b.FStar_Syntax_Syntax.sort in
                                                           let uu___11 =
                                                             is_unit_t b_t in
                                                           if uu___11
                                                           then
                                                             FStar_Compiler_Effect.op_Less_Bar
                                                               FStar_Tactics_Monad.ret
                                                               (((FStar_Syntax_Util.exp_unit,
                                                                   aq) ::
                                                                 uvs), imps,
                                                                 ((FStar_Syntax_Syntax.NT
                                                                    (b,
                                                                    FStar_Syntax_Util.exp_unit))
                                                                 :: subst))
                                                           else
                                                             (let uv_deps =
                                                                if
                                                                  Prims.op_Negation
                                                                    tm_uses_subtyping
                                                                then []
                                                                else
                                                                  (let b_t_uvs
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    b_t in
                                                                   let uu___14
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    imps
                                                                    (FStar_Compiler_List.filter
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    (uu___16,
                                                                    uv) ->
                                                                    FStar_Compiler_Util.set_mem
                                                                    uv
                                                                    b_t_uvs)) in
                                                                   FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___14
                                                                    (FStar_Compiler_List.map
                                                                    FStar_Pervasives_Native.snd)) in
                                                              let uu___13 =
                                                                FStar_Tactics_Monad.new_uvar
                                                                  "apply_lemma"
                                                                  env1 b_t
                                                                  FStar_Pervasives_Native.None
                                                                  uv_deps
                                                                  (rangeof
                                                                    goal) in
                                                              FStar_Tactics_Monad.bind
                                                                uu___13
                                                                (fun uu___14
                                                                   ->
                                                                   match uu___14
                                                                   with
                                                                   | 
                                                                   (t1, u) ->
                                                                    ((
                                                                    let uu___16
                                                                    =
                                                                    FStar_Compiler_Effect.op_Less_Bar
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "2635") in
                                                                    if
                                                                    uu___16
                                                                    then
                                                                    let uu___17
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    u in
                                                                    let uu___18
                                                                    =
                                                                    FStar_Compiler_List.fold_left
                                                                    (fun acc
                                                                    ->
                                                                    fun uv ->
                                                                    let uu___19
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    uv in
                                                                    FStar_Compiler_Util.format2
                                                                    "%s; %s"
                                                                    acc
                                                                    uu___19)
                                                                    ""
                                                                    uv_deps in
                                                                    let uu___19
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    tm1 in
                                                                    let uu___20
                                                                    =
                                                                    FStar_Compiler_Util.string_of_bool
                                                                    tm_uses_subtyping in
                                                                    FStar_Compiler_Util.print4
                                                                    "Apply lemma created a new uvar %s and made it depend on %s while applying %s (uses_subtyping: %s)\n"
                                                                    uu___17
                                                                    uu___18
                                                                    uu___19
                                                                    uu___20
                                                                    else ());
                                                                    FStar_Compiler_Effect.op_Less_Bar
                                                                    FStar_Tactics_Monad.ret
                                                                    (((t1,
                                                                    aq) ::
                                                                    uvs),
                                                                    ((t1, u)
                                                                    :: imps),
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b, t1))
                                                                    ::
                                                                    subst))))))
                                                  ([], [], []) bs in
                                              FStar_Tactics_Monad.bind uu___7
                                                (fun uu___8 ->
                                                   match uu___8 with
                                                   | (uvs, implicits1, subst)
                                                       ->
                                                       let implicits2 =
                                                         FStar_Compiler_List.rev
                                                           implicits1 in
                                                       let uvs1 =
                                                         FStar_Compiler_List.rev
                                                           uvs in
                                                       let pre1 =
                                                         FStar_Syntax_Subst.subst
                                                           subst pre in
                                                       let post1 =
                                                         FStar_Syntax_Subst.subst
                                                           subst post in
                                                       let post_u =
                                                         env1.FStar_TypeChecker_Env.universe_of
                                                           env1 post1 in
                                                       let cmp_func =
                                                         if noinst
                                                         then do_match
                                                         else
                                                           if noinst_lhs
                                                           then
                                                             do_match_on_lhs
                                                           else do_unify in
                                                       let uu___9 =
                                                         let uu___10 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal in
                                                         let uu___11 =
                                                           FStar_Syntax_Util.mk_squash
                                                             post_u post1 in
                                                         cmp_func env1
                                                           uu___10 uu___11 in
                                                       FStar_Tactics_Monad.bind
                                                         uu___9
                                                         (fun b ->
                                                            if
                                                              Prims.op_Negation
                                                                b
                                                            then
                                                              let uu___10 =
                                                                let uu___11 =
                                                                  FStar_Syntax_Util.mk_squash
                                                                    post_u
                                                                    post1 in
                                                                let uu___12 =
                                                                  FStar_Tactics_Types.goal_type
                                                                    goal in
                                                                FStar_TypeChecker_Err.print_discrepancy
                                                                  (tts env1)
                                                                  uu___11
                                                                  uu___12 in
                                                              match uu___10
                                                              with
                                                              | (post2,
                                                                 goalt) ->
                                                                  let uu___11
                                                                    =
                                                                    tts env1
                                                                    tm1 in
                                                                  fail3
                                                                    "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                    uu___11
                                                                    post2
                                                                    goalt
                                                            else
                                                              (let uu___11 =
                                                                 solve' goal
                                                                   FStar_Syntax_Util.exp_unit in
                                                               FStar_Tactics_Monad.bind
                                                                 uu___11
                                                                 (fun uu___12
                                                                    ->
                                                                    let is_free_uvar
                                                                    uv t1 =
                                                                    let free_uvars
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1 in
                                                                    FStar_Compiler_Util.set_elements
                                                                    uu___14 in
                                                                    FStar_Compiler_List.map
                                                                    (fun x ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu___13 in
                                                                    FStar_Compiler_List.existsML
                                                                    (fun u ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars in
                                                                    let appears
                                                                    uv goals
                                                                    =
                                                                    FStar_Compiler_List.existsML
                                                                    (fun g'
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g' in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu___13)
                                                                    goals in
                                                                    let checkone
                                                                    t1 goals
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1 in
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu___14)
                                                                    ->
                                                                    (match 
                                                                    hd.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,
                                                                    uu___15)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu___15
                                                                    -> false) in
                                                                    let uu___13
                                                                    =
                                                                    let must_tot
                                                                    = false in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    implicits2
                                                                    (check_apply_implicits_solutions
                                                                    true env1
                                                                    (FStar_Pervasives_Native.Some
                                                                    goal)
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    "apply_lemma"
                                                                    must_tot) in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu___13
                                                                    (fun
                                                                    sub_goals
                                                                    ->
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
                                                                    let uu___14
                                                                    = f x xs1 in
                                                                    if
                                                                    uu___14
                                                                    then
                                                                    let uu___15
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu___15
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g ->
                                                                    fun goals
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g in
                                                                    checkone
                                                                    uu___15
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu___14)
                                                                    sub_goals1 in
                                                                    let uu___14
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    env1
                                                                    guard
                                                                    (rangeof
                                                                    goal) in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu___14
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    let pre_u
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 pre1 in
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStar_TypeChecker_Common.NonTrivial
                                                                    pre1) in
                                                                    FStar_TypeChecker_Rel.simplify_guard
                                                                    env1
                                                                    uu___19 in
                                                                    uu___18.FStar_TypeChecker_Common.guard_f in
                                                                    match uu___17
                                                                    with
                                                                    | 
                                                                    FStar_TypeChecker_Common.Trivial
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    ()
                                                                    | 
                                                                    FStar_TypeChecker_Common.NonTrivial
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Monad.add_irrelevant_goal
                                                                    goal
                                                                    "apply_lemma precondition"
                                                                    env1 pre1 in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu___16
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Monad.add_goals
                                                                    sub_goals2))))))))))))) in
          focus uu___1 in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "apply_lemma") uu___
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
let (push_bvs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env)
  =
  fun e ->
    fun bvs ->
      FStar_Compiler_List.fold_left
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
        let uu___ =
          let uu___1 = FStar_Tactics_Types.goal_env g in split_env b1 uu___1 in
        match uu___ with
        | FStar_Pervasives_Native.Some (e0, b11, bvs) ->
            let bs =
              FStar_Compiler_List.map FStar_Syntax_Syntax.mk_binder (b11 ::
                bvs) in
            let t = FStar_Tactics_Types.goal_type g in
            let uu___1 =
              let uu___2 = FStar_Syntax_Subst.close_binders bs in
              let uu___3 = FStar_Syntax_Subst.close bs t in (uu___2, uu___3) in
            (match uu___1 with
             | (bs', t') ->
                 let bs'1 =
                   let uu___2 = FStar_Syntax_Syntax.mk_binder b2 in
                   let uu___3 = FStar_Compiler_List.tail bs' in uu___2 ::
                     uu___3 in
                 let uu___2 = FStar_Syntax_Subst.open_term bs'1 t' in
                 (match uu___2 with
                  | (bs'', t'') ->
                      let b21 =
                        let uu___3 = FStar_Compiler_List.hd bs'' in
                        uu___3.FStar_Syntax_Syntax.binder_bv in
                      let new_env =
                        let uu___3 =
                          FStar_Compiler_List.map
                            (fun b -> b.FStar_Syntax_Syntax.binder_bv) bs'' in
                        push_bvs e0 uu___3 in
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = should_check_goal_uvar g in
                          FStar_Pervasives_Native.Some uu___5 in
                        FStar_Tactics_Monad.new_uvar "subst_goal" new_env t''
                          uu___4
                          (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_apply_tac_prefix
                          (rangeof g) in
                      FStar_Tactics_Monad.bind uu___3
                        (fun uu___4 ->
                           match uu___4 with
                           | (uvt, uv) ->
                               let goal' =
                                 FStar_Tactics_Types.mk_goal new_env uv
                                   g.FStar_Tactics_Types.opts
                                   g.FStar_Tactics_Types.is_guard
                                   g.FStar_Tactics_Types.label in
                               let sol =
                                 let uu___5 =
                                   FStar_Syntax_Util.abs bs'' uvt
                                     FStar_Pervasives_Native.None in
                                 let uu___6 =
                                   FStar_Compiler_List.map
                                     (fun uu___7 ->
                                        match uu___7 with
                                        | {
                                            FStar_Syntax_Syntax.binder_bv =
                                              bv;
                                            FStar_Syntax_Syntax.binder_qual =
                                              q;
                                            FStar_Syntax_Syntax.binder_attrs
                                              = uu___8;_}
                                            ->
                                            let uu___9 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                bv in
                                            FStar_Syntax_Syntax.as_arg uu___9)
                                     bs in
                                 FStar_Syntax_Util.mk_app uu___5 uu___6 in
                               let uu___5 = set_solution g sol in
                               FStar_Tactics_Monad.bind uu___5
                                 (fun uu___6 ->
                                    FStar_Tactics_Monad.ret
                                      (FStar_Pervasives_Native.Some
                                         (b21, goal'))))))
        | FStar_Pervasives_Native.None ->
            FStar_Tactics_Monad.ret FStar_Pervasives_Native.None
let (rewrite : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun h ->
    let uu___ =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let bv = h.FStar_Syntax_Syntax.binder_bv in
           FStar_Tactics_Monad.mlog
             (fun uu___1 ->
                let uu___2 = FStar_Syntax_Print.bv_to_string bv in
                let uu___3 =
                  FStar_Syntax_Print.term_to_string
                    bv.FStar_Syntax_Syntax.sort in
                FStar_Compiler_Util.print2 "+++Rewrite %s : %s\n" uu___2
                  uu___3)
             (fun uu___1 ->
                let uu___2 =
                  let uu___3 = FStar_Tactics_Types.goal_env goal in
                  split_env bv uu___3 in
                match uu___2 with
                | FStar_Pervasives_Native.None ->
                    FStar_Tactics_Monad.fail
                      "binder not found in environment"
                | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                    let uu___3 =
                      let uu___4 = whnf e0 bv1.FStar_Syntax_Syntax.sort in
                      destruct_eq uu___4 in
                    (match uu___3 with
                     | FStar_Pervasives_Native.Some (x, e) ->
                         let uu___4 =
                           let uu___5 = FStar_Syntax_Subst.compress x in
                           uu___5.FStar_Syntax_Syntax.n in
                         (match uu___4 with
                          | FStar_Syntax_Syntax.Tm_name x1 ->
                              let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                              let t = FStar_Tactics_Types.goal_type goal in
                              let bs =
                                FStar_Compiler_List.map
                                  FStar_Syntax_Syntax.mk_binder bvs in
                              let uu___5 =
                                let uu___6 =
                                  FStar_Syntax_Subst.close_binders bs in
                                let uu___7 = FStar_Syntax_Subst.close bs t in
                                (uu___6, uu___7) in
                              (match uu___5 with
                               | (bs', t') ->
                                   let uu___6 =
                                     let uu___7 =
                                       FStar_Syntax_Subst.subst_binders s bs' in
                                     let uu___8 =
                                       FStar_Syntax_Subst.subst s t' in
                                     (uu___7, uu___8) in
                                   (match uu___6 with
                                    | (bs'1, t'1) ->
                                        let uu___7 =
                                          FStar_Syntax_Subst.open_term bs'1
                                            t'1 in
                                        (match uu___7 with
                                         | (bs'', t'') ->
                                             let new_env =
                                               let uu___8 =
                                                 let uu___9 =
                                                   FStar_Compiler_List.map
                                                     (fun b ->
                                                        b.FStar_Syntax_Syntax.binder_bv)
                                                     bs'' in
                                                 bv1 :: uu___9 in
                                               push_bvs e0 uu___8 in
                                             let uu___8 =
                                               let uu___9 =
                                                 let uu___10 =
                                                   should_check_goal_uvar
                                                     goal in
                                                 FStar_Pervasives_Native.Some
                                                   uu___10 in
                                               FStar_Tactics_Monad.new_uvar
                                                 "rewrite" new_env t'' uu___9
                                                 (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_apply_tac_prefix
                                                 (rangeof goal) in
                                             FStar_Tactics_Monad.bind uu___8
                                               (fun uu___9 ->
                                                  match uu___9 with
                                                  | (uvt, uv) ->
                                                      let goal' =
                                                        FStar_Tactics_Types.mk_goal
                                                          new_env uv
                                                          goal.FStar_Tactics_Types.opts
                                                          goal.FStar_Tactics_Types.is_guard
                                                          goal.FStar_Tactics_Types.label in
                                                      let sol =
                                                        let uu___10 =
                                                          FStar_Syntax_Util.abs
                                                            bs'' uvt
                                                            FStar_Pervasives_Native.None in
                                                        let uu___11 =
                                                          FStar_Compiler_List.map
                                                            (fun uu___12 ->
                                                               match uu___12
                                                               with
                                                               | {
                                                                   FStar_Syntax_Syntax.binder_bv
                                                                    = bv2;
                                                                   FStar_Syntax_Syntax.binder_qual
                                                                    = uu___13;
                                                                   FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___14;_}
                                                                   ->
                                                                   let uu___15
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv2 in
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    uu___15)
                                                            bs in
                                                        FStar_Syntax_Util.mk_app
                                                          uu___10 uu___11 in
                                                      let uu___10 =
                                                        set_solution goal sol in
                                                      FStar_Tactics_Monad.bind
                                                        uu___10
                                                        (fun uu___11 ->
                                                           FStar_Tactics_Monad.replace_cur
                                                             goal')))))
                          | uu___5 ->
                              FStar_Tactics_Monad.fail
                                "Not an equality hypothesis with a variable on the LHS")
                     | uu___4 ->
                         FStar_Tactics_Monad.fail
                           "Not an equality hypothesis"))) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "rewrite") uu___
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac)
  =
  fun b ->
    fun s ->
      let uu___ =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let bv = b.FStar_Syntax_Syntax.binder_bv in
             let bv' =
               let uu___1 =
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       FStar_Ident.range_of_id bv.FStar_Syntax_Syntax.ppname in
                     (s, uu___4) in
                   FStar_Ident.mk_ident uu___3 in
                 {
                   FStar_Syntax_Syntax.ppname = uu___2;
                   FStar_Syntax_Syntax.index = (bv.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = (bv.FStar_Syntax_Syntax.sort)
                 } in
               FStar_Syntax_Syntax.freshen_bv uu___1 in
             let uu___1 = subst_goal bv bv' goal in
             FStar_Tactics_Monad.bind uu___1
               (fun uu___2 ->
                  match uu___2 with
                  | FStar_Pervasives_Native.None ->
                      FStar_Tactics_Monad.fail
                        "binder not found in environment"
                  | FStar_Pervasives_Native.Some (bv'1, goal1) ->
                      let uu___3 = FStar_Tactics_Monad.replace_cur goal1 in
                      FStar_Tactics_Monad.bind uu___3
                        (fun uu___4 ->
                           FStar_Tactics_Monad.ret
                             {
                               FStar_Syntax_Syntax.binder_bv = bv'1;
                               FStar_Syntax_Syntax.binder_qual =
                                 (b.FStar_Syntax_Syntax.binder_qual);
                               FStar_Syntax_Syntax.binder_attrs =
                                 (b.FStar_Syntax_Syntax.binder_attrs)
                             }))) in
      FStar_Compiler_Effect.op_Less_Bar
        (FStar_Tactics_Monad.wrap_err "rename_to") uu___
let (binder_retype :
  FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let uu___ =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let bv = b.FStar_Syntax_Syntax.binder_bv in
           let uu___1 =
             let uu___2 = FStar_Tactics_Types.goal_env goal in
             split_env bv uu___2 in
           match uu___1 with
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail
                 "binder is not present in environment"
           | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
               let uu___2 = FStar_Syntax_Util.type_u () in
               (match uu___2 with
                | (ty, u) ->
                    let uu___3 =
                      let uu___4 =
                        let uu___5 = should_check_goal_uvar goal in
                        FStar_Pervasives_Native.Some uu___5 in
                      FStar_Tactics_Monad.new_uvar "binder_retype" e0 ty
                        uu___4
                        (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_apply_tac_prefix
                        (rangeof goal) in
                    FStar_Tactics_Monad.bind uu___3
                      (fun uu___4 ->
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
                                     FStar_Syntax_Syntax.bv_to_name bv'' in
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
                                      FStar_Syntax_Syntax.sort = uu___5
                                    }) bvs in
                             let env' = push_bvs e0 (bv'' :: bvs1) in
                             FStar_Tactics_Monad.bind
                               FStar_Tactics_Monad.dismiss
                               (fun uu___5 ->
                                  let new_goal =
                                    let uu___6 =
                                      FStar_Tactics_Types.goal_with_env goal
                                        env' in
                                    let uu___7 =
                                      let uu___8 =
                                        FStar_Tactics_Types.goal_type goal in
                                      FStar_Syntax_Subst.subst s uu___8 in
                                    goal_with_type uu___6 uu___7 in
                                  let uu___6 =
                                    FStar_Tactics_Monad.add_goals [new_goal] in
                                  FStar_Tactics_Monad.bind uu___6
                                    (fun uu___7 ->
                                       let uu___8 =
                                         FStar_Syntax_Util.mk_eq2
                                           (FStar_Syntax_Syntax.U_succ u) ty
                                           bv1.FStar_Syntax_Syntax.sort t' in
                                       FStar_Tactics_Monad.add_irrelevant_goal
                                         goal "binder_retype equation" e0
                                         uu___8))))) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "binder_retype") uu___
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    fun b ->
      let uu___ =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let bv = b.FStar_Syntax_Syntax.binder_bv in
             let uu___1 =
               let uu___2 = FStar_Tactics_Types.goal_env goal in
               split_env bv uu___2 in
             match uu___1 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail
                   "binder is not present in environment"
             | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                 let steps =
                   let uu___2 = FStar_TypeChecker_Cfg.translate_norm_steps s in
                   FStar_Compiler_List.op_At
                     [FStar_TypeChecker_Env.Reify;
                     FStar_TypeChecker_Env.UnfoldTac] uu___2 in
                 let sort' = normalize steps e0 bv1.FStar_Syntax_Syntax.sort in
                 let bv' =
                   {
                     FStar_Syntax_Syntax.ppname =
                       (bv1.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (bv1.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = sort'
                   } in
                 let env' = push_bvs e0 (bv' :: bvs) in
                 let uu___2 = FStar_Tactics_Types.goal_with_env goal env' in
                 FStar_Tactics_Monad.replace_cur uu___2) in
      FStar_Compiler_Effect.op_Less_Bar
        (FStar_Tactics_Monad.wrap_err "norm_binder_type") uu___
let (revert : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu___1 =
           let uu___2 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu___2 in
         match uu___1 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot revert; empty context"
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
               FStar_Tactics_Monad.new_uvar "revert" env' typ' uu___3
                 (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_apply_tac_prefix
                 (rangeof goal) in
             FStar_Tactics_Monad.bind uu___2
               (fun uu___3 ->
                  match uu___3 with
                  | (r, u_r) ->
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              let uu___8 = FStar_Syntax_Syntax.bv_to_name x in
                              FStar_Syntax_Syntax.as_arg uu___8 in
                            [uu___7] in
                          let uu___7 =
                            let uu___8 = FStar_Tactics_Types.goal_type goal in
                            uu___8.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.mk_Tm_app r uu___6 uu___7 in
                        set_solution goal uu___5 in
                      FStar_Tactics_Monad.bind uu___4
                        (fun uu___5 ->
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
      let uu___ = FStar_Syntax_Free.names t in
      FStar_Compiler_Util.set_mem bv uu___
let (clear : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let bv = b.FStar_Syntax_Syntax.binder_bv in
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu___ ->
              let uu___1 = FStar_Syntax_Print.binder_to_string b in
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.all_binders uu___5 in
                  FStar_Compiler_Effect.op_Bar_Greater uu___4
                    FStar_Compiler_List.length in
                FStar_Compiler_Effect.op_Bar_Greater uu___3
                  FStar_Compiler_Util.string_of_int in
              FStar_Compiler_Util.print2
                "Clear of (%s), env has %s binders\n" uu___1 uu___2)
           (fun uu___ ->
              let uu___1 =
                let uu___2 = FStar_Tactics_Types.goal_env goal in
                split_env bv uu___2 in
              match uu___1 with
              | FStar_Pervasives_Native.None ->
                  FStar_Tactics_Monad.fail
                    "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e', bv1, bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> FStar_Tactics_Monad.ret ()
                    | bv'::bvs2 ->
                        let uu___2 = free_in bv1 bv'.FStar_Syntax_Syntax.sort in
                        if uu___2
                        then
                          let uu___3 =
                            let uu___4 = FStar_Syntax_Print.bv_to_string bv' in
                            FStar_Compiler_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu___4 in
                          FStar_Tactics_Monad.fail uu___3
                        else check bvs2 in
                  let uu___2 =
                    let uu___3 = FStar_Tactics_Types.goal_type goal in
                    free_in bv1 uu___3 in
                  if uu___2
                  then
                    FStar_Tactics_Monad.fail
                      "Cannot clear; binder present in goal"
                  else
                    (let uu___4 = check bvs in
                     FStar_Tactics_Monad.bind uu___4
                       (fun uu___5 ->
                          let env' = push_bvs e' bvs in
                          let uu___6 =
                            let uu___7 = FStar_Tactics_Types.goal_type goal in
                            let uu___8 =
                              let uu___9 = should_check_goal_uvar goal in
                              FStar_Pervasives_Native.Some uu___9 in
                            FStar_Tactics_Monad.new_uvar "clear.witness" env'
                              uu___7 uu___8
                              (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_apply_tac_prefix
                              (rangeof goal) in
                          FStar_Tactics_Monad.bind uu___6
                            (fun uu___7 ->
                               match uu___7 with
                               | (ut, uvar_ut) ->
                                   let uu___8 = set_solution goal ut in
                                   FStar_Tactics_Monad.bind uu___8
                                     (fun uu___9 ->
                                        let uu___10 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label in
                                        FStar_Tactics_Monad.replace_cur
                                          uu___10))))))
let (clear_top : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu___1 =
           let uu___2 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu___2 in
         match uu___1 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x, uu___2) ->
             let uu___3 = FStar_Syntax_Syntax.mk_binder x in clear uu___3)
let (prune : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu___ = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu___ in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (addns : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu___ = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.add_proof_ns ctx uu___ in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
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
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun g ->
             let attempt l1 r1 =
               let uu___ =
                 let uu___1 = FStar_Tactics_Types.goal_env g in
                 do_unify' allow_guards uu___1 l1 r1 in
               FStar_Tactics_Monad.bind uu___
                 (fun uu___1 ->
                    match uu___1 with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.ret false
                    | FStar_Pervasives_Native.Some guard ->
                        let uu___2 = solve' g FStar_Syntax_Util.exp_unit in
                        FStar_Tactics_Monad.bind uu___2
                          (fun uu___3 ->
                             if allow_guards
                             then
                               let uu___4 =
                                 let uu___5 = FStar_Tactics_Types.goal_env g in
                                 let uu___6 = guard_formula guard in
                                 FStar_Tactics_Monad.goal_of_guard "t_trefl"
                                   uu___5 uu___6 (rangeof g) in
                               FStar_Tactics_Monad.bind uu___4
                                 (fun goal ->
                                    let uu___5 =
                                      FStar_Tactics_Monad.push_goals [goal] in
                                    FStar_Tactics_Monad.bind uu___5
                                      (fun uu___6 ->
                                         FStar_Tactics_Monad.ret true))
                             else
                               (let uu___5 =
                                  FStar_TypeChecker_Env.is_trivial_guard_formula
                                    guard in
                                if uu___5
                                then FStar_Tactics_Monad.ret true
                                else
                                  failwith
                                    "internal error: _t_refl: guard is not trivial"))) in
             let uu___ = attempt l r in
             FStar_Tactics_Monad.bind uu___
               (fun uu___1 ->
                  if uu___1
                  then FStar_Tactics_Monad.ret ()
                  else
                    (let norm1 =
                       let uu___2 = FStar_Tactics_Types.goal_env g in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.UnfoldUntil
                            FStar_Syntax_Syntax.delta_constant;
                         FStar_TypeChecker_Env.Primops;
                         FStar_TypeChecker_Env.UnfoldTac] uu___2 in
                     let uu___2 =
                       let uu___3 = norm1 l in
                       let uu___4 = norm1 r in attempt uu___3 uu___4 in
                     FStar_Tactics_Monad.bind uu___2
                       (fun uu___3 ->
                          if uu___3
                          then FStar_Tactics_Monad.ret ()
                          else
                            (let uu___4 =
                               let uu___5 =
                                 let uu___6 = FStar_Tactics_Types.goal_env g in
                                 tts uu___6 in
                               FStar_TypeChecker_Err.print_discrepancy uu___5
                                 l r in
                             match uu___4 with
                             | (ls, rs) ->
                                 fail2 "cannot unify (%s) and (%s)" ls rs)))))
let (t_trefl : Prims.bool -> unit FStar_Tactics_Monad.tac) =
  fun allow_guards ->
    let uu___ =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu___1 =
             let uu___2 =
               let uu___3 = FStar_Tactics_Types.goal_env g in
               let uu___4 = FStar_Tactics_Types.goal_type g in
               whnf uu___3 uu___4 in
             destruct_eq uu___2 in
           match uu___1 with
           | FStar_Pervasives_Native.Some (l, r) -> _t_trefl allow_guards l r
           | FStar_Pervasives_Native.None ->
               let uu___2 =
                 let uu___3 = FStar_Tactics_Types.goal_env g in
                 let uu___4 = FStar_Tactics_Types.goal_type g in
                 tts uu___3 uu___4 in
               fail1 "not an equality (%s)" uu___2) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "t_trefl") uu___
let (dup : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let env1 = FStar_Tactics_Types.goal_env g in
         let uu___1 =
           let uu___2 = FStar_Tactics_Types.goal_type g in
           let uu___3 =
             let uu___4 = should_check_goal_uvar g in
             FStar_Pervasives_Native.Some uu___4 in
           FStar_Tactics_Monad.new_uvar "dup" env1 uu___2 uu___3
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_apply_tac_prefix
             (rangeof g) in
         FStar_Tactics_Monad.bind uu___1
           (fun uu___2 ->
              match uu___2 with
              | (u, u_uvar) ->
                  (mark_uvar_as_allow_untyped
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
                    FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                      (fun uu___4 ->
                         let t_eq =
                           let uu___5 =
                             let uu___6 = FStar_Tactics_Types.goal_type g in
                             env1.FStar_TypeChecker_Env.universe_of env1
                               uu___6 in
                           let uu___6 = FStar_Tactics_Types.goal_type g in
                           let uu___7 = FStar_Tactics_Types.goal_witness g in
                           FStar_Syntax_Util.mk_eq2 uu___5 uu___6 u uu___7 in
                         let uu___5 =
                           FStar_Tactics_Monad.add_irrelevant_goal g
                             "dup equation" env1 t_eq in
                         FStar_Tactics_Monad.bind uu___5
                           (fun uu___6 ->
                              let uu___7 = FStar_Tactics_Monad.add_goals [g'] in
                              FStar_Tactics_Monad.bind uu___7
                                (fun uu___8 -> FStar_Tactics_Monad.ret ())))))))
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
              if uu___ then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu___ -> (acc, l11, l21) in
        let uu___ = aux [] l1 l2 in
        match uu___ with
        | (pr, t1, t2) -> ((FStar_Compiler_List.rev pr), t1, t2)
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal ->
      FStar_Tactics_Types.goal FStar_Tactics_Monad.tac)
  =
  fun g1 ->
    fun g2 ->
      let close_forall_no_univs bs f =
        FStar_Compiler_List.fold_right
          (fun b ->
             fun f1 ->
               FStar_Syntax_Util.mk_forall_no_univ
                 b.FStar_Syntax_Syntax.binder_bv f1) bs f in
      let uu___ = FStar_Tactics_Types.get_phi g1 in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          FStar_Tactics_Monad.fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu___1 = FStar_Tactics_Types.get_phi g2 in
          (match uu___1 with
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let uu___2 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_Compiler_List.rev gamma1)
                   (FStar_Compiler_List.rev gamma2) in
               (match uu___2 with
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
                    let uu___3 = set_solution g1 FStar_Syntax_Util.exp_unit in
                    FStar_Tactics_Monad.bind uu___3
                      (fun uu___4 ->
                         let uu___5 =
                           set_solution g2 FStar_Syntax_Util.exp_unit in
                         FStar_Tactics_Monad.bind uu___5
                           (fun uu___6 ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2 in
                              let nenv =
                                let uu___7 = FStar_Tactics_Types.goal_env g1 in
                                let uu___8 =
                                  FStar_Compiler_Util.smap_create
                                    (Prims.of_int (100)) in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___7.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___7.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___7.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_Compiler_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___7.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache = uu___8;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___7.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___7.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___7.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___7.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___7.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___7.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___7.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___7.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___7.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___7.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___7.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___7.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___7.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___7.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___7.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___7.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___7.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___7.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___7.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___7.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                    =
                                    (uu___7.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___7.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                    =
                                    (uu___7.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.teq_nosmt_force =
                                    (uu___7.FStar_TypeChecker_Env.teq_nosmt_force);
                                  FStar_TypeChecker_Env.subtype_nosmt_force =
                                    (uu___7.FStar_TypeChecker_Env.subtype_nosmt_force);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___7.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___7.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___7.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___7.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___7.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___7.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___7.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___7.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___7.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___7.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___7.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___7.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___7.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___7.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___7.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___7.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___7.FStar_TypeChecker_Env.enable_defer_to_tac);
                                  FStar_TypeChecker_Env.unif_allow_ref_guards
                                    =
                                    (uu___7.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                  FStar_TypeChecker_Env.erase_erasable_args =
                                    (uu___7.FStar_TypeChecker_Env.erase_erasable_args);
                                  FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar
                                    =
                                    (uu___7.FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar)
                                } in
                              let uu___7 =
                                FStar_Tactics_Monad.mk_irrelevant_goal
                                  "joined" nenv ng (rangeof g1)
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label in
                              FStar_Tactics_Monad.bind uu___7
                                (fun goal ->
                                   FStar_Tactics_Monad.mlog
                                     (fun uu___8 ->
                                        let uu___9 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g1 in
                                        let uu___10 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g2 in
                                        let uu___11 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            goal in
                                        FStar_Compiler_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu___9 uu___10 uu___11)
                                     (fun uu___8 ->
                                        FStar_Tactics_Monad.ret goal))))))
let (join : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
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
                   FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
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
             FStar_Tactics_Monad.bind uu___1
               (fun uu___2 ->
                  let uu___3 = join_goals g1 g2 in
                  FStar_Tactics_Monad.bind uu___3
                    (fun g12 -> FStar_Tactics_Monad.add_goals [g12]))
         | uu___1 -> FStar_Tactics_Monad.fail "join: less than 2 goals")
let (set_options : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    let uu___ =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
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
                 FStar_Tactics_Monad.replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s))) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "set_options") uu___
let (top_env : unit -> env FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
           ps.FStar_Tactics_Types.main_context)
let (lax_on : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let uu___1 =
           (FStar_Options.lax ()) ||
             (let uu___2 = FStar_Tactics_Types.goal_env g in
              uu___2.FStar_TypeChecker_Env.lax) in
         FStar_Tactics_Monad.ret uu___1)
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun tm ->
      let uu___ =
        FStar_Tactics_Monad.mlog
          (fun uu___1 ->
             let uu___2 = FStar_Syntax_Print.term_to_string tm in
             FStar_Compiler_Util.print1 "unquote: tm = %s\n" uu___2)
          (fun uu___1 ->
             FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
               (fun goal ->
                  let env1 =
                    let uu___2 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.set_expected_typ uu___2 ty in
                  let uu___2 = __tc_ghost env1 tm in
                  FStar_Tactics_Monad.bind uu___2
                    (fun uu___3 ->
                       match uu___3 with
                       | (tm1, typ, guard) ->
                           FStar_Tactics_Monad.mlog
                             (fun uu___4 ->
                                let uu___5 =
                                  FStar_Syntax_Print.term_to_string tm1 in
                                FStar_Compiler_Util.print1
                                  "unquote: tm' = %s\n" uu___5)
                             (fun uu___4 ->
                                FStar_Tactics_Monad.mlog
                                  (fun uu___5 ->
                                     let uu___6 =
                                       FStar_Syntax_Print.term_to_string typ in
                                     FStar_Compiler_Util.print1
                                       "unquote: typ = %s\n" uu___6)
                                  (fun uu___5 ->
                                     let uu___6 =
                                       proc_guard "unquote" env1 guard
                                         (rangeof goal) in
                                     FStar_Tactics_Monad.bind uu___6
                                       (fun uu___7 ->
                                          FStar_Tactics_Monad.ret tm1)))))) in
      FStar_Compiler_Effect.op_Less_Bar
        (FStar_Tactics_Monad.wrap_err "unquote") uu___
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun ty ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           let uu___ =
             match ty with
             | FStar_Pervasives_Native.Some ty1 ->
                 let env2 =
                   let uu___1 =
                     let uu___2 = FStar_Syntax_Util.type_u () in
                     FStar_Compiler_Effect.op_Bar_Greater uu___2
                       FStar_Pervasives_Native.fst in
                   FStar_TypeChecker_Env.set_expected_typ env1 uu___1 in
                 let uu___1 = __tc_ghost env2 ty1 in
                 FStar_Tactics_Monad.bind uu___1
                   (fun uu___2 ->
                      match uu___2 with
                      | (ty2, uu___3, g) ->
                          FStar_Tactics_Monad.ret
                            (ty2, g, (ty2.FStar_Syntax_Syntax.pos)))
             | FStar_Pervasives_Native.None ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = FStar_Syntax_Util.type_u () in
                     FStar_Compiler_Effect.op_Less_Bar
                       FStar_Pervasives_Native.fst uu___3 in
                   FStar_Tactics_Monad.new_uvar "uvar_env.2" env1 uu___2
                     FStar_Pervasives_Native.None []
                     ps.FStar_Tactics_Types.entry_range in
                 FStar_Tactics_Monad.bind uu___1
                   (fun uu___2 ->
                      match uu___2 with
                      | (typ, uvar_typ) ->
                          FStar_Tactics_Monad.ret
                            (typ, FStar_TypeChecker_Env.trivial_guard,
                              FStar_Compiler_Range.dummyRange)) in
           FStar_Tactics_Monad.bind uu___
             (fun uu___1 ->
                match uu___1 with
                | (typ, g, r) ->
                    let uu___2 = proc_guard "uvar_env_typ" env1 g r in
                    FStar_Tactics_Monad.bind uu___2
                      (fun uu___3 ->
                         let uu___4 =
                           FStar_Tactics_Monad.new_uvar "uvar_env" env1 typ
                             FStar_Pervasives_Native.None []
                             ps.FStar_Tactics_Types.entry_range in
                         FStar_Tactics_Monad.bind uu___4
                           (fun uu___5 ->
                              match uu___5 with
                              | (t, uvar_t) -> FStar_Tactics_Monad.ret t))))
let (fresh_universe_uvar :
  unit -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStar_Syntax_Util.type_u () in
      FStar_Compiler_Effect.op_Bar_Greater uu___2 FStar_Pervasives_Native.fst in
    FStar_Compiler_Effect.op_Bar_Greater uu___1 FStar_Tactics_Monad.ret
let (unshelve : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu___ =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
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
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (env1.FStar_TypeChecker_Env.use_bv_sorts);
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
                   FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar =
                     (env1.FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar)
                 } in
               let g =
                 FStar_Tactics_Types.mk_goal env2 ctx_uvar opts false "" in
               let g1 = bnorm_goal g in FStar_Tactics_Monad.add_goals [g1]
           | uu___2 -> FStar_Tactics_Monad.fail "not a uvar") in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "unshelve") uu___
let (tac_and :
  Prims.bool FStar_Tactics_Monad.tac ->
    Prims.bool FStar_Tactics_Monad.tac -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let comp =
        FStar_Tactics_Monad.bind t1
          (fun b ->
             let uu___ = if b then t2 else FStar_Tactics_Monad.ret false in
             FStar_Tactics_Monad.bind uu___
               (fun b' ->
                  if b'
                  then FStar_Tactics_Monad.ret b'
                  else FStar_Tactics_Monad.fail "")) in
      let uu___ = FStar_Tactics_Monad.trytac comp in
      FStar_Tactics_Monad.bind uu___
        (fun uu___1 ->
           match uu___1 with
           | FStar_Pervasives_Native.Some (true) ->
               FStar_Tactics_Monad.ret true
           | FStar_Pervasives_Native.Some (false) -> failwith "impossible"
           | FStar_Pervasives_Native.None -> FStar_Tactics_Monad.ret false)
let (match_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu___1 = __tc e t1 in
               FStar_Tactics_Monad.bind uu___1
                 (fun uu___2 ->
                    match uu___2 with
                    | (t11, ty1, g1) ->
                        let uu___3 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu___3
                          (fun uu___4 ->
                             match uu___4 with
                             | (t21, ty2, g2) ->
                                 let uu___5 =
                                   proc_guard "match_env g1" e g1
                                     ps.FStar_Tactics_Types.entry_range in
                                 FStar_Tactics_Monad.bind uu___5
                                   (fun uu___6 ->
                                      let uu___7 =
                                        proc_guard "match_env g2" e g2
                                          ps.FStar_Tactics_Types.entry_range in
                                      FStar_Tactics_Monad.bind uu___7
                                        (fun uu___8 ->
                                           let uu___9 = do_match e ty1 ty2 in
                                           let uu___10 = do_match e t11 t21 in
                                           tac_and uu___9 uu___10))))) in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "match_env") uu___
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu___1 = __tc e t1 in
               FStar_Tactics_Monad.bind uu___1
                 (fun uu___2 ->
                    match uu___2 with
                    | (t11, ty1, g1) ->
                        let uu___3 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu___3
                          (fun uu___4 ->
                             match uu___4 with
                             | (t21, ty2, g2) ->
                                 let uu___5 =
                                   proc_guard "unify_env g1" e g1
                                     ps.FStar_Tactics_Types.entry_range in
                                 FStar_Tactics_Monad.bind uu___5
                                   (fun uu___6 ->
                                      let uu___7 =
                                        proc_guard "unify_env g2" e g2
                                          ps.FStar_Tactics_Types.entry_range in
                                      FStar_Tactics_Monad.bind uu___7
                                        (fun uu___8 ->
                                           let uu___9 = do_unify e ty1 ty2 in
                                           let uu___10 = do_unify e t11 t21 in
                                           tac_and uu___9 uu___10))))) in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "unify_env") uu___
let (unify_guard_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu___1 = __tc e t1 in
               FStar_Tactics_Monad.bind uu___1
                 (fun uu___2 ->
                    match uu___2 with
                    | (t11, ty1, g1) ->
                        let uu___3 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu___3
                          (fun uu___4 ->
                             match uu___4 with
                             | (t21, ty2, g2) ->
                                 let uu___5 =
                                   proc_guard "unify_guard_env g1" e g1
                                     ps.FStar_Tactics_Types.entry_range in
                                 FStar_Tactics_Monad.bind uu___5
                                   (fun uu___6 ->
                                      let uu___7 =
                                        proc_guard "unify_guard_env g2" e g2
                                          ps.FStar_Tactics_Types.entry_range in
                                      FStar_Tactics_Monad.bind uu___7
                                        (fun uu___8 ->
                                           let uu___9 =
                                             do_unify' true e ty1 ty2 in
                                           FStar_Tactics_Monad.bind uu___9
                                             (fun uu___10 ->
                                                match uu___10 with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Tactics_Monad.ret
                                                      false
                                                | FStar_Pervasives_Native.Some
                                                    g11 ->
                                                    let uu___11 =
                                                      do_unify' true e t11
                                                        t21 in
                                                    FStar_Tactics_Monad.bind
                                                      uu___11
                                                      (fun uu___12 ->
                                                         match uu___12 with
                                                         | FStar_Pervasives_Native.None
                                                             ->
                                                             FStar_Tactics_Monad.ret
                                                               false
                                                         | FStar_Pervasives_Native.Some
                                                             g21 ->
                                                             let formula =
                                                               let uu___13 =
                                                                 guard_formula
                                                                   g11 in
                                                               let uu___14 =
                                                                 guard_formula
                                                                   g21 in
                                                               FStar_Syntax_Util.mk_conj
                                                                 uu___13
                                                                 uu___14 in
                                                             let uu___13 =
                                                               FStar_Tactics_Monad.goal_of_guard
                                                                 "unify_guard_env.g2"
                                                                 e formula
                                                                 ps.FStar_Tactics_Types.entry_range in
                                                             FStar_Tactics_Monad.bind
                                                               uu___13
                                                               (fun goal ->
                                                                  let uu___14
                                                                    =
                                                                    FStar_Tactics_Monad.push_goals
                                                                    [goal] in
                                                                  FStar_Tactics_Monad.bind
                                                                    uu___14
                                                                    (
                                                                    fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    true))))))))) in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "unify_guard_env") uu___
let (launch_process :
  Prims.string ->
    Prims.string Prims.list ->
      Prims.string -> Prims.string FStar_Tactics_Monad.tac)
  =
  fun prog ->
    fun args ->
      fun input ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu___ ->
             let uu___1 = FStar_Options.unsafe_tactic_exec () in
             if uu___1
             then
               let s =
                 FStar_Compiler_Util.run_process "tactic_launch" prog args
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
        (fun uu___ ->
           let uu___1 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t in
           FStar_Tactics_Monad.ret uu___1)
let (change : FStar_Reflection_Data.typ -> unit FStar_Tactics_Monad.tac) =
  fun ty ->
    let uu___ =
      FStar_Tactics_Monad.mlog
        (fun uu___1 ->
           let uu___2 = FStar_Syntax_Print.term_to_string ty in
           FStar_Compiler_Util.print1 "change: ty = %s\n" uu___2)
        (fun uu___1 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                let uu___2 =
                  let uu___3 = FStar_Tactics_Types.goal_env g in
                  __tc uu___3 ty in
                FStar_Tactics_Monad.bind uu___2
                  (fun uu___3 ->
                     match uu___3 with
                     | (ty1, uu___4, guard) ->
                         let uu___5 =
                           let uu___6 = FStar_Tactics_Types.goal_env g in
                           proc_guard "change" uu___6 guard (rangeof g) in
                         FStar_Tactics_Monad.bind uu___5
                           (fun uu___6 ->
                              let uu___7 =
                                let uu___8 = FStar_Tactics_Types.goal_env g in
                                let uu___9 = FStar_Tactics_Types.goal_type g in
                                do_unify uu___8 uu___9 ty1 in
                              FStar_Tactics_Monad.bind uu___7
                                (fun bb ->
                                   if bb
                                   then
                                     let uu___8 = goal_with_type g ty1 in
                                     FStar_Tactics_Monad.replace_cur uu___8
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops] in
                                      let ng =
                                        let uu___9 =
                                          FStar_Tactics_Types.goal_env g in
                                        let uu___10 =
                                          FStar_Tactics_Types.goal_type g in
                                        normalize steps uu___9 uu___10 in
                                      let nty =
                                        let uu___9 =
                                          FStar_Tactics_Types.goal_env g in
                                        normalize steps uu___9 ty1 in
                                      let uu___9 =
                                        let uu___10 =
                                          FStar_Tactics_Types.goal_env g in
                                        do_unify uu___10 ng nty in
                                      FStar_Tactics_Monad.bind uu___9
                                        (fun b ->
                                           if b
                                           then
                                             let uu___10 =
                                               goal_with_type g ty1 in
                                             FStar_Tactics_Monad.replace_cur
                                               uu___10
                                           else
                                             FStar_Tactics_Monad.fail
                                               "not convertible"))))))) in
    FStar_Compiler_Effect.op_Less_Bar (FStar_Tactics_Monad.wrap_err "change")
      uu___
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
    let uu___ =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu___1 =
             let uu___2 = FStar_Tactics_Types.goal_env g in __tc uu___2 s_tm in
           FStar_Tactics_Monad.bind uu___1
             (fun uu___2 ->
                match uu___2 with
                | (s_tm1, s_ty, guard) ->
                    let uu___3 =
                      let uu___4 = FStar_Tactics_Types.goal_env g in
                      proc_guard "destruct" uu___4 guard (rangeof g) in
                    FStar_Tactics_Monad.bind uu___3
                      (fun uu___4 ->
                         let s_ty1 =
                           let uu___5 = FStar_Tactics_Types.goal_env g in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant] uu___5
                             s_ty in
                         let uu___5 =
                           let uu___6 = FStar_Syntax_Util.unrefine s_ty1 in
                           FStar_Syntax_Util.head_and_args_full uu___6 in
                         match uu___5 with
                         | (h, args) ->
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 = FStar_Syntax_Subst.compress h in
                                 uu___8.FStar_Syntax_Syntax.n in
                               match uu___7 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   FStar_Tactics_Monad.ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu___8;
                                      FStar_Syntax_Syntax.vars = uu___9;
                                      FStar_Syntax_Syntax.hash_code = uu___10;_},
                                    us)
                                   -> FStar_Tactics_Monad.ret (fv, us)
                               | uu___8 ->
                                   FStar_Tactics_Monad.fail
                                     "type is not an fv" in
                             FStar_Tactics_Monad.bind uu___6
                               (fun uu___7 ->
                                  match uu___7 with
                                  | (fv, a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv in
                                      let uu___8 =
                                        let uu___9 =
                                          FStar_Tactics_Types.goal_env g in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu___9 t_lid in
                                      (match uu___8 with
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
                                                let uu___9 =
                                                  erasable &&
                                                    (let uu___10 =
                                                       FStar_Tactics_Types.is_irrelevant
                                                         g in
                                                     Prims.op_Negation
                                                       uu___10) in
                                                failwhen uu___9
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu___10 ->
                                                     failwhen
                                                       ((FStar_Compiler_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_Compiler_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu___11 ->
                                                          let uu___12 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty in
                                                          match uu___12 with
                                                          | (t_ps1, t_ty1) ->
                                                              let uu___13 =
                                                                FStar_Tactics_Monad.mapM
                                                                  (fun c_lid
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu___15
                                                                    c_lid in
                                                                    match uu___14
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
                                                                    ((FStar_Compiler_List.length
                                                                    a_us) <>
                                                                    (FStar_Compiler_List.length
                                                                    c_us))
                                                                    "t_us don't match?"
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty in
                                                                    let uu___16
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1) in
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    (c_us1,
                                                                    c_ty2) ->
                                                                    let uu___17
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2 in
                                                                    (match uu___17
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    comp) ->
                                                                    let uu___18
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname in
                                                                    let ppname1
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    ppname in
                                                                    Prims.op_Hat
                                                                    "a"
                                                                    uu___21 in
                                                                    let uu___21
                                                                    =
                                                                    FStar_Ident.range_of_id
                                                                    ppname in
                                                                    (uu___20,
                                                                    uu___21) in
                                                                    FStar_Ident.mk_ident
                                                                    uu___19 in
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
                                                                    let uu___19
                                                                    =
                                                                    rename_bv
                                                                    b.FStar_Syntax_Syntax.binder_bv in
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = uu___19;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    =
                                                                    (b.FStar_Syntax_Syntax.binder_qual);
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    =
                                                                    (b.FStar_Syntax_Syntax.binder_attrs)
                                                                    }) bs in
                                                                    let subst
                                                                    =
                                                                    FStar_Compiler_List.map2
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    fun
                                                                    uu___20
                                                                    ->
                                                                    match 
                                                                    (uu___19,
                                                                    uu___20)
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___21;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___22;_},
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv';
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___23;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___24;_})
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv' in
                                                                    (bv,
                                                                    uu___26) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu___25)
                                                                    bs bs' in
                                                                    let uu___19
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs' in
                                                                    let uu___20
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst
                                                                    comp in
                                                                    (uu___19,
                                                                    uu___20) in
                                                                    (match uu___18
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    comp1) ->
                                                                    let uu___19
                                                                    =
                                                                    FStar_Compiler_List.splitAt
                                                                    nparam
                                                                    bs1 in
                                                                    (match uu___19
                                                                    with
                                                                    | 
                                                                    (d_ps,
                                                                    bs2) ->
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1 in
                                                                    Prims.op_Negation
                                                                    uu___21 in
                                                                    failwhen
                                                                    uu___20
                                                                    "not total?"
                                                                    (fun
                                                                    uu___21
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
                                                                    uu___22 =
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu___23)
                                                                    -> true
                                                                    | 
                                                                    uu___23
                                                                    -> false in
                                                                    let uu___22
                                                                    =
                                                                    FStar_Compiler_List.splitAt
                                                                    nparam
                                                                    args in
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    (a_ps,
                                                                    a_is) ->
                                                                    failwhen
                                                                    ((FStar_Compiler_List.length
                                                                    a_ps) <>
                                                                    (FStar_Compiler_List.length
                                                                    d_ps))
                                                                    "params not match?"
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_Compiler_List.zip
                                                                    d_ps a_ps in
                                                                    let subst
                                                                    =
                                                                    FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___25;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___26;_},
                                                                    (t,
                                                                    uu___27))
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
                                                                    uu___24
                                                                    ->
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___25;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___26;_},
                                                                    (t,
                                                                    uu___27))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (bv, t))),
                                                                    true))
                                                                    d_ps_a_ps in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = bq;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___25;_}
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
                                                                    let uu___24
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
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.use_bv_sorts);
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
                                                                    FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar)
                                                                    } s_ty1
                                                                    pat in
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    (uu___25,
                                                                    uu___26,
                                                                    uu___27,
                                                                    uu___28,
                                                                    pat_t,
                                                                    uu___29,
                                                                    _guard_pat,
                                                                    _erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    uu___31 in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu___30 in
                                                                    let cod1
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b in
                                                                    [uu___31] in
                                                                    let uu___31
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu___30
                                                                    uu___31 in
                                                                    let nty =
                                                                    let uu___30
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu___30 in
                                                                    let uu___30
                                                                    =
                                                                    FStar_Tactics_Monad.new_uvar
                                                                    "destruct branch"
                                                                    env1 nty
                                                                    FStar_Pervasives_Native.None
                                                                    []
                                                                    (rangeof
                                                                    g) in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu___30
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    match uu___31
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
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit in
                                                                    [uu___33] in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu___32 in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1) in
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_Compiler_List.length
                                                                    bs3) in
                                                                    (fv1,
                                                                    uu___34) in
                                                                    (g', br,
                                                                    uu___33) in
                                                                    FStar_Tactics_Monad.ret
                                                                    uu___32)))))))
                                                                    | 
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids in
                                                              FStar_Tactics_Monad.bind
                                                                uu___13
                                                                (fun goal_brs
                                                                   ->
                                                                   let uu___14
                                                                    =
                                                                    FStar_Compiler_List.unzip3
                                                                    goal_brs in
                                                                   match uu___14
                                                                   with
                                                                   | 
                                                                   (goals,
                                                                    brs,
                                                                    infos) ->
                                                                    let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    FStar_Pervasives_Native.None,
                                                                    brs,
                                                                    FStar_Pervasives_Native.None))
                                                                    s_tm1.FStar_Syntax_Syntax.pos in
                                                                    let uu___15
                                                                    =
                                                                    solve' g
                                                                    w in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu___15
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    mark_goal_implicit_allow_untyped
                                                                    g;
                                                                    (
                                                                    let uu___18
                                                                    =
                                                                    FStar_Tactics_Monad.add_goals
                                                                    goals in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu___18
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    infos))))))
                                            | uu___9 ->
                                                FStar_Tactics_Monad.fail
                                                  "not an inductive type")))))) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "destruct") uu___
let (gather_explicit_guards_for_resolved_goals :
  unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      let uu___2 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps ->
             let goals_of_resolved_implicits =
               FStar_Compiler_List.filter_map
                 (fun i ->
                    let uu___3 =
                      (FStar_TypeChecker_Rel.is_implicit_resolved
                         ps.FStar_Tactics_Types.main_context i)
                        &&
                        (let uu___4 =
                           FStar_TypeChecker_Rel.check_implicit_solution_for_tac
                             ps.FStar_Tactics_Types.main_context i in
                         FStar_Pervasives_Native.uu___is_Some uu___4) in
                    if uu___3
                    then
                      let g =
                        FStar_Tactics_Types.goal_of_implicit
                          ps.FStar_Tactics_Types.main_context i in
                      let uu___4 =
                        let uu___5 = FStar_Tactics_Types.goal_witness g in
                        (uu___5, (g.FStar_Tactics_Types.goal_ctx_uvar)) in
                      FStar_Pervasives_Native.Some uu___4
                    else FStar_Pervasives_Native.None)
                 ps.FStar_Tactics_Types.all_implicits in
             let uu___3 =
               check_apply_implicits_solutions false
                 ps.FStar_Tactics_Types.main_context
                 FStar_Pervasives_Native.None
                 ps.FStar_Tactics_Types.tac_verb_dbg
                 "gather_explicit_guards_for_resolved_goals" true
                 goals_of_resolved_implicits in
             FStar_Tactics_Monad.bind uu___3
               (fun sub_goals ->
                  let sub_goals1 = FStar_Compiler_List.flatten sub_goals in
                  FStar_Tactics_Monad.add_goals sub_goals1)) in
      FStar_Compiler_Effect.op_Less_Bar
        (with_policy FStar_Tactics_Types.Goal) uu___2 in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err
         "gather_explicit_guards_for_resolved_goals") uu___1
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
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Tactics_Monad.tac)
  =
  fun t ->
    let uu___ =
      let uu___1 = top_env () in
      FStar_Tactics_Monad.bind uu___1
        (fun e ->
           let t1 = FStar_Syntax_Util.unascribe t in
           let t2 = FStar_Syntax_Util.unlazy_emb t1 in
           match t2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_meta (t3, uu___2) -> inspect t3
           | FStar_Syntax_Syntax.Tm_name bv ->
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Var bv)
           | FStar_Syntax_Syntax.Tm_bvar bv ->
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_BVar bv)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_FVar fv)
           | FStar_Syntax_Syntax.Tm_uinst (t3, us) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStar_Compiler_Effect.op_Bar_Greater t3
                       FStar_Syntax_Subst.compress in
                   FStar_Compiler_Effect.op_Bar_Greater uu___4
                     FStar_Syntax_Util.unascribe in
                 uu___3.FStar_Syntax_Syntax.n in
               (match uu___2 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_UInst (fv, us))
                | uu___3 ->
                    failwith "Tac::inspect: Tm_uinst head not an fvar")
           | FStar_Syntax_Syntax.Tm_app (hd, []) ->
               failwith "empty arguments on Tm_app"
           | FStar_Syntax_Syntax.Tm_app (hd, args) ->
               let uu___2 = last args in
               (match uu___2 with
                | (a, q) ->
                    let q' = FStar_Reflection_Basic.inspect_aqual q in
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = init args in
                          FStar_Syntax_Syntax.mk_Tm_app hd uu___6
                            t2.FStar_Syntax_Syntax.pos in
                        (uu___5, (a, q')) in
                      FStar_Reflection_Data.Tv_App uu___4 in
                    FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                      uu___3)
           | FStar_Syntax_Syntax.Tm_abs ([], uu___2, uu___3) ->
               failwith "empty arguments on Tm_abs"
           | FStar_Syntax_Syntax.Tm_abs (bs, t3, k) ->
               let uu___2 = FStar_Syntax_Subst.open_term bs t3 in
               (match uu___2 with
                | (bs1, t4) ->
                    (match bs1 with
                     | [] -> failwith "impossible"
                     | b::bs2 ->
                         let uu___3 =
                           let uu___4 =
                             let uu___5 = FStar_Syntax_Util.abs bs2 t4 k in
                             (b, uu___5) in
                           FStar_Reflection_Data.Tv_Abs uu___4 in
                         FStar_Compiler_Effect.op_Less_Bar
                           FStar_Tactics_Monad.ret uu___3))
           | FStar_Syntax_Syntax.Tm_type u ->
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Type u)
           | FStar_Syntax_Syntax.Tm_arrow ([], k) ->
               failwith "empty binders on arrow"
           | FStar_Syntax_Syntax.Tm_arrow uu___2 ->
               let uu___3 = FStar_Syntax_Util.arrow_one t2 in
               (match uu___3 with
                | FStar_Pervasives_Native.Some (b, c) ->
                    FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Arrow (b, c))
                | FStar_Pervasives_Native.None -> failwith "impossible")
           | FStar_Syntax_Syntax.Tm_refine (bv, t3) ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu___2 = FStar_Syntax_Subst.open_term [b] t3 in
               (match uu___2 with
                | (b', t4) ->
                    let b1 =
                      match b' with
                      | b'1::[] -> b'1
                      | uu___3 -> failwith "impossible" in
                    FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Refine
                         ((b1.FStar_Syntax_Syntax.binder_bv), t4)))
           | FStar_Syntax_Syntax.Tm_constant c ->
               let uu___2 =
                 let uu___3 = FStar_Reflection_Basic.inspect_const c in
                 FStar_Reflection_Data.Tv_Const uu___3 in
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 uu___2
           | FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       FStar_Syntax_Unionfind.uvar_id
                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                     FStar_BigInt.of_int_fs uu___5 in
                   (uu___4, (ctx_u, s)) in
                 FStar_Reflection_Data.Tv_Uvar uu___3 in
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 uu___2
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Pervasives.Inr uu___3 ->
                      FStar_Compiler_Effect.op_Less_Bar
                        FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Pervasives.Inl bv ->
                      let b = FStar_Syntax_Syntax.mk_binder bv in
                      let uu___3 = FStar_Syntax_Subst.open_term [b] t21 in
                      (match uu___3 with
                       | (bs, t22) ->
                           let b1 =
                             match bs with
                             | b2::[] -> b2
                             | uu___4 ->
                                 failwith
                                   "impossible: open_term returned different amount of binders" in
                           FStar_Compiler_Effect.op_Less_Bar
                             FStar_Tactics_Monad.ret
                             (FStar_Reflection_Data.Tv_Let
                                (false, (lb.FStar_Syntax_Syntax.lbattrs),
                                  (b1.FStar_Syntax_Syntax.binder_bv),
                                  (lb.FStar_Syntax_Syntax.lbdef), t22))))
           | FStar_Syntax_Syntax.Tm_let ((true, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Pervasives.Inr uu___3 ->
                      FStar_Compiler_Effect.op_Less_Bar
                        FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Pervasives.Inl bv ->
                      let uu___3 = FStar_Syntax_Subst.open_let_rec [lb] t21 in
                      (match uu___3 with
                       | (lbs, t22) ->
                           (match lbs with
                            | lb1::[] ->
                                (match lb1.FStar_Syntax_Syntax.lbname with
                                 | FStar_Pervasives.Inr uu___4 ->
                                     FStar_Tactics_Monad.ret
                                       FStar_Reflection_Data.Tv_Unknown
                                 | FStar_Pervasives.Inl bv1 ->
                                     FStar_Compiler_Effect.op_Less_Bar
                                       FStar_Tactics_Monad.ret
                                       (FStar_Reflection_Data.Tv_Let
                                          (true,
                                            (lb1.FStar_Syntax_Syntax.lbattrs),
                                            bv1,
                                            (lb1.FStar_Syntax_Syntax.lbdef),
                                            t22)))
                            | uu___4 ->
                                failwith
                                  "impossible: open_term returned different amount of binders")))
           | FStar_Syntax_Syntax.Tm_match (t3, ret_opt, brs, uu___2) ->
               let rec inspect_pat p =
                 match p.FStar_Syntax_Syntax.v with
                 | FStar_Syntax_Syntax.Pat_constant c ->
                     let uu___3 = FStar_Reflection_Basic.inspect_const c in
                     FStar_Reflection_Data.Pat_Constant uu___3
                 | FStar_Syntax_Syntax.Pat_cons (fv, us_opt, ps) ->
                     let uu___3 =
                       let uu___4 =
                         FStar_Compiler_List.map
                           (fun uu___5 ->
                              match uu___5 with
                              | (p1, b) ->
                                  let uu___6 = inspect_pat p1 in (uu___6, b))
                           ps in
                       (fv, us_opt, uu___4) in
                     FStar_Reflection_Data.Pat_Cons uu___3
                 | FStar_Syntax_Syntax.Pat_var bv ->
                     FStar_Reflection_Data.Pat_Var bv
                 | FStar_Syntax_Syntax.Pat_wild bv ->
                     FStar_Reflection_Data.Pat_Wild bv
                 | FStar_Syntax_Syntax.Pat_dot_term (bv, t4) ->
                     FStar_Reflection_Data.Pat_Dot_Term (bv, t4) in
               let brs1 =
                 FStar_Compiler_List.map FStar_Syntax_Subst.open_branch brs in
               let brs2 =
                 FStar_Compiler_List.map
                   (fun uu___3 ->
                      match uu___3 with
                      | (pat, uu___4, t4) ->
                          let uu___5 = inspect_pat pat in (uu___5, t4)) brs1 in
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Match (t3, ret_opt, brs2))
           | FStar_Syntax_Syntax.Tm_unknown ->
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 FStar_Reflection_Data.Tv_Unknown
           | uu___2 ->
               ((let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.tag_of_term t2 in
                     let uu___7 = term_to_string e t2 in
                     FStar_Compiler_Util.format2
                       "inspect: outside of expected syntax (%s, %s)\n"
                       uu___6 uu___7 in
                   (FStar_Errors.Warning_CantInspect, uu___5) in
                 FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu___4);
                FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                  FStar_Reflection_Data.Tv_Unknown)) in
    FStar_Tactics_Monad.wrap_err "inspect" uu___
let (pack' :
  FStar_Reflection_Data.term_view ->
    Prims.bool -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun tv ->
    fun leave_curried ->
      match tv with
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu___ = FStar_Syntax_Syntax.bv_to_name bv in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu___ = FStar_Syntax_Syntax.bv_to_tm bv in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu___ = FStar_Syntax_Syntax.fv_to_tm fv in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_UInst (fv, us) ->
          let uu___ =
            let uu___1 = FStar_Syntax_Syntax.fv_to_tm fv in
            FStar_Syntax_Syntax.mk_Tm_uinst uu___1 us in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_App (l, (r, q)) ->
          let q' = FStar_Reflection_Basic.pack_aqual q in
          let uu___ = FStar_Syntax_Util.mk_app l [(r, q')] in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_Abs (b, t) ->
          let uu___ =
            FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_Arrow (b, c) ->
          let uu___ =
            if leave_curried
            then FStar_Syntax_Util.arrow [b] c
            else
              (let uu___2 = FStar_Syntax_Util.arrow [b] c in
               FStar_Syntax_Util.canon_arrow uu___2) in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_Type u ->
          let uu___ =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
              FStar_Compiler_Range.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_Refine (bv, t) ->
          let uu___ = FStar_Syntax_Util.refine bv t in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_Const c ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Reflection_Basic.pack_const c in
              FStar_Syntax_Syntax.Tm_constant uu___2 in
            FStar_Syntax_Syntax.mk uu___1 FStar_Compiler_Range.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_Uvar (_u, ctx_u_s) ->
          let uu___ =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
              FStar_Compiler_Range.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_Let (false, attrs, bv, t1, t2) ->
          let lb =
            FStar_Syntax_Util.mk_letbinding (FStar_Pervasives.Inl bv) []
              bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid
              t1 attrs FStar_Compiler_Range.dummyRange in
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 = FStar_Syntax_Syntax.mk_binder bv in [uu___5] in
                  FStar_Syntax_Subst.close uu___4 t2 in
                ((false, [lb]), uu___3) in
              FStar_Syntax_Syntax.Tm_let uu___2 in
            FStar_Syntax_Syntax.mk uu___1 FStar_Compiler_Range.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_Let (true, attrs, bv, t1, t2) ->
          let lb =
            FStar_Syntax_Util.mk_letbinding (FStar_Pervasives.Inl bv) []
              bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid
              t1 attrs FStar_Compiler_Range.dummyRange in
          let uu___ = FStar_Syntax_Subst.close_let_rec [lb] t2 in
          (match uu___ with
           | (lbs, body) ->
               let uu___1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                   FStar_Compiler_Range.dummyRange in
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 uu___1)
      | FStar_Reflection_Data.Tv_Match (t, ret_opt, brs) ->
          let wrap v =
            {
              FStar_Syntax_Syntax.v = v;
              FStar_Syntax_Syntax.p = FStar_Compiler_Range.dummyRange
            } in
          let rec pack_pat p =
            match p with
            | FStar_Reflection_Data.Pat_Constant c ->
                let uu___ =
                  let uu___1 = FStar_Reflection_Basic.pack_const c in
                  FStar_Syntax_Syntax.Pat_constant uu___1 in
                FStar_Compiler_Effect.op_Less_Bar wrap uu___
            | FStar_Reflection_Data.Pat_Cons (fv, us_opt, ps) ->
                let uu___ =
                  let uu___1 =
                    let uu___2 =
                      FStar_Compiler_List.map
                        (fun uu___3 ->
                           match uu___3 with
                           | (p1, b) ->
                               let uu___4 = pack_pat p1 in (uu___4, b)) ps in
                    (fv, us_opt, uu___2) in
                  FStar_Syntax_Syntax.Pat_cons uu___1 in
                FStar_Compiler_Effect.op_Less_Bar wrap uu___
            | FStar_Reflection_Data.Pat_Var bv ->
                FStar_Compiler_Effect.op_Less_Bar wrap
                  (FStar_Syntax_Syntax.Pat_var bv)
            | FStar_Reflection_Data.Pat_Wild bv ->
                FStar_Compiler_Effect.op_Less_Bar wrap
                  (FStar_Syntax_Syntax.Pat_wild bv)
            | FStar_Reflection_Data.Pat_Dot_Term (bv, t1) ->
                FStar_Compiler_Effect.op_Less_Bar wrap
                  (FStar_Syntax_Syntax.Pat_dot_term (bv, t1)) in
          let brs1 =
            FStar_Compiler_List.map
              (fun uu___ ->
                 match uu___ with
                 | (pat, t1) ->
                     let uu___1 = pack_pat pat in
                     (uu___1, FStar_Pervasives_Native.None, t1)) brs in
          let brs2 =
            FStar_Compiler_List.map FStar_Syntax_Subst.close_branch brs1 in
          let uu___ =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_match
                 (t, ret_opt, brs2, FStar_Pervasives_Native.None))
              FStar_Compiler_Range.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt, use_eq) ->
          let uu___ =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_ascribed
                 (e, ((FStar_Pervasives.Inl t), tacopt, use_eq),
                   FStar_Pervasives_Native.None))
              FStar_Compiler_Range.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt, use_eq) ->
          let uu___ =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_ascribed
                 (e, ((FStar_Pervasives.Inr c), tacopt, use_eq),
                   FStar_Pervasives_Native.None))
              FStar_Compiler_Range.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_Data.Tv_Unknown ->
          let uu___ =
            FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
              FStar_Compiler_Range.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
let (pack :
  FStar_Reflection_Data.term_view ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  = fun tv -> pack' tv false
let (pack_curried :
  FStar_Reflection_Data.term_view ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  = fun tv -> pack' tv true
let (lget :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun k ->
      let uu___ =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps ->
             let uu___1 =
               FStar_Compiler_Util.psmap_try_find
                 ps.FStar_Tactics_Types.local_state k in
             match uu___1 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t) in
      FStar_Compiler_Effect.op_Less_Bar (FStar_Tactics_Monad.wrap_err "lget")
        uu___
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun _ty ->
    fun k ->
      fun t ->
        let uu___ =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let ps1 =
                 let uu___1 =
                   FStar_Compiler_Util.psmap_add
                     ps.FStar_Tactics_Types.local_state k t in
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
               FStar_Tactics_Monad.set ps1) in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "lset") uu___
let (set_urgency : FStar_BigInt.t -> unit FStar_Tactics_Monad.tac) =
  fun u ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
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
         FStar_Tactics_Monad.set ps1)
let (t_commute_applied_match : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu___2 =
             let uu___3 =
               let uu___4 = FStar_Tactics_Types.goal_env g in
               let uu___5 = FStar_Tactics_Types.goal_type g in
               whnf uu___4 uu___5 in
             destruct_eq uu___3 in
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
                     | FStar_Syntax_Syntax.Tm_match (e, asc_opt, brs, lopt)
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
                           FStar_Compiler_Effect.op_Bar_Greater lopt
                             (FStar_Compiler_Util.map_option
                                (fun rc ->
                                   let uu___5 =
                                     FStar_Compiler_Effect.op_Bar_Greater
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Compiler_Util.map_option
                                          (fun t ->
                                             let uu___6 =
                                               let uu___7 =
                                                 FStar_Tactics_Types.goal_env
                                                   g in
                                               FStar_TypeChecker_Normalize.get_n_binders
                                                 uu___7
                                                 (FStar_Compiler_List.length
                                                    las) t in
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
                                                        c2))) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (rc.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu___5;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (rc.FStar_Syntax_Syntax.residual_flags)
                                   })) in
                         let l' =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_match
                                (e, asc_opt, brs', lopt'))
                             l.FStar_Syntax_Syntax.pos in
                         let uu___5 =
                           let uu___6 = FStar_Tactics_Types.goal_env g in
                           do_unify' false uu___6 l' r in
                         FStar_Tactics_Monad.bind uu___5
                           (fun uu___6 ->
                              match uu___6 with
                              | FStar_Pervasives_Native.None ->
                                  FStar_Tactics_Monad.fail
                                    "discharging the equality failed"
                              | FStar_Pervasives_Native.Some guard ->
                                  let uu___7 =
                                    FStar_TypeChecker_Env.is_trivial_guard_formula
                                      guard in
                                  if uu___7
                                  then
                                    (mark_uvar_as_allow_untyped
                                       g.FStar_Tactics_Types.goal_ctx_uvar;
                                     solve g FStar_Syntax_Util.exp_unit)
                                  else
                                    failwith
                                      "internal error: _t_refl: guard is not trivial")
                     | uu___5 ->
                         FStar_Tactics_Monad.fail "lhs is not a match"))
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail "not an equality") in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "t_commute_applied_match") uu___1
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
            FStar_TypeChecker_Env.use_bv_sorts =
              (env2.FStar_TypeChecker_Env.use_bv_sorts);
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
            FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar =
              (env2.FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar)
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
            FStar_TypeChecker_Env.use_bv_sorts =
              (env3.FStar_TypeChecker_Env.use_bv_sorts);
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
            FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar =
              (env3.FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar)
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
            FStar_TypeChecker_Env.use_bv_sorts =
              (env4.FStar_TypeChecker_Env.use_bv_sorts);
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
            FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar =
              (env4.FStar_TypeChecker_Env.rel_query_for_apply_tac_uvar)
          } in
        env5
let (proofstate_of_goals :
  FStar_Compiler_Range.range ->
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
              FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
              FStar_Tactics_Types.entry_range = rng;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
              FStar_Tactics_Types.freshness = Prims.int_zero;
              FStar_Tactics_Types.tac_verb_dbg = uu___;
              FStar_Tactics_Types.local_state = uu___1;
              FStar_Tactics_Types.urgency = Prims.int_one
            } in
          ps
let (proofstate_of_goal_ty :
  FStar_Compiler_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env1 ->
      fun typ ->
        let env2 = tac_env env1 in
        let uu___ = FStar_Tactics_Types.goal_of_goal_ty env2 typ in
        match uu___ with
        | (g, g_u) ->
            let ps =
              proofstate_of_goals rng env2 [g]
                g_u.FStar_TypeChecker_Common.implicits in
            let uu___1 = FStar_Tactics_Types.goal_witness g in (ps, uu___1)
let (proofstate_of_all_implicits :
  FStar_Compiler_Range.range ->
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
            FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
            FStar_Tactics_Types.entry_range = rng;
            FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
            FStar_Tactics_Types.freshness = Prims.int_zero;
            FStar_Tactics_Types.tac_verb_dbg = uu___;
            FStar_Tactics_Types.local_state = uu___1;
            FStar_Tactics_Types.urgency = Prims.int_one
          } in
        (ps, w)