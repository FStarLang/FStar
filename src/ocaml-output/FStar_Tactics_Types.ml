open Prims
type goal =
  {
  goal_main_env: FStar_TypeChecker_Env.env ;
  goal_ctx_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  opts: FStar_Options.optionstate ;
  is_guard: Prims.bool ;
  label: Prims.string }
let (__proj__Mkgoal__item__goal_main_env : goal -> FStar_TypeChecker_Env.env)
  =
  fun projectee ->
    match projectee with
    | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} ->
        goal_main_env
let (__proj__Mkgoal__item__goal_ctx_uvar :
  goal -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee ->
    match projectee with
    | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} ->
        goal_ctx_uvar
let (__proj__Mkgoal__item__opts : goal -> FStar_Options.optionstate) =
  fun projectee ->
    match projectee with
    | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} -> opts
let (__proj__Mkgoal__item__is_guard : goal -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} -> is_guard
let (__proj__Mkgoal__item__label : goal -> Prims.string) =
  fun projectee ->
    match projectee with
    | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} -> label
let (goal_env : goal -> FStar_TypeChecker_Env.env) = fun g -> g.goal_main_env
let (goal_witness : goal -> FStar_Syntax_Syntax.term) =
  fun g ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uvar
         ((g.goal_ctx_uvar), ([], FStar_Syntax_Syntax.NoUseRange)))
      FStar_Range.dummyRange
let (goal_type : goal -> FStar_Syntax_Syntax.term) =
  fun g -> (g.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
let (goal_with_type : goal -> FStar_Syntax_Syntax.term -> goal) =
  fun g ->
    fun t ->
      let c = g.goal_ctx_uvar in
      let c' =
        let uu___ = c in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = t;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_meta)
        } in
      let uu___ = g in
      {
        goal_main_env = (uu___.goal_main_env);
        goal_ctx_uvar = c';
        opts = (uu___.opts);
        is_guard = (uu___.is_guard);
        label = (uu___.label)
      }
let (goal_with_env : goal -> FStar_TypeChecker_Env.env -> goal) =
  fun g ->
    fun env ->
      let c = g.goal_ctx_uvar in
      let c' =
        let uu___ = c in
        let uu___1 = FStar_TypeChecker_Env.all_binders env in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (env.FStar_TypeChecker_Env.gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders = uu___1;
          FStar_Syntax_Syntax.ctx_uvar_typ =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_typ);
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_meta)
        } in
      let uu___ = g in
      {
        goal_main_env = env;
        goal_ctx_uvar = c';
        opts = (uu___.opts);
        is_guard = (uu___.is_guard);
        label = (uu___.label)
      }
let (goal_of_ctx_uvar : goal -> FStar_Syntax_Syntax.ctx_uvar -> goal) =
  fun g ->
    fun ctx_u ->
      let uu___ = g in
      {
        goal_main_env = (uu___.goal_main_env);
        goal_ctx_uvar = ctx_u;
        opts = (uu___.opts);
        is_guard = (uu___.is_guard);
        label = (uu___.label)
      }
let (mk_goal :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Options.optionstate -> Prims.bool -> Prims.string -> goal)
  =
  fun env ->
    fun u ->
      fun o ->
        fun b ->
          fun l ->
            {
              goal_main_env = env;
              goal_ctx_uvar = u;
              opts = o;
              is_guard = b;
              label = l
            }
let (goal_of_goal_ty :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> (goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun typ ->
      let uu___ =
        FStar_TypeChecker_Env.new_implicit_var_aux "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
          FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None in
      match uu___ with
      | (u, ctx_uvars, g_u) ->
          let uu___1 = FStar_List.hd ctx_uvars in
          (match uu___1 with
           | (ctx_uvar, uu___2) ->
               let g =
                 let uu___3 = FStar_Options.peek () in
                 mk_goal env ctx_uvar uu___3 false "" in
               (g, g_u))
let (goal_of_implicit :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.implicit -> goal) =
  fun env ->
    fun i ->
      let uu___ = FStar_Options.peek () in
      mk_goal
        (let uu___1 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range = (uu___1.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             ((i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___1.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___1.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit = (uu___1.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = (uu___1.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
             (uu___1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
           FStar_TypeChecker_Env.universe_of =
             (uu___1.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
             (uu___1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___1.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___1.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv = (uu___1.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe = (uu___1.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___1.FStar_TypeChecker_Env.enable_defer_to_tac);
           FStar_TypeChecker_Env.unif_allow_ref_guards =
             (uu___1.FStar_TypeChecker_Env.unif_allow_ref_guards)
         }) i.FStar_TypeChecker_Common.imp_uvar uu___ false
        i.FStar_TypeChecker_Common.imp_reason
let (rename_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binder Prims.list ->
      FStar_Syntax_Syntax.binder Prims.list)
  =
  fun subst ->
    fun bs ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu___ ->
              let x = uu___.FStar_Syntax_Syntax.binder_bv in
              let y =
                let uu___1 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Subst.subst subst uu___1 in
              let uu___1 =
                let uu___2 = FStar_Syntax_Subst.compress y in
                uu___2.FStar_Syntax_Syntax.n in
              match uu___1 with
              | FStar_Syntax_Syntax.Tm_name y1 ->
                  let uu___2 = uu___ in
                  let uu___3 =
                    let uu___4 = uu___.FStar_Syntax_Syntax.binder_bv in
                    let uu___5 =
                      FStar_Syntax_Subst.subst subst
                        x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___4.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___4.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu___5
                    } in
                  {
                    FStar_Syntax_Syntax.binder_bv = uu___3;
                    FStar_Syntax_Syntax.binder_qual =
                      (uu___2.FStar_Syntax_Syntax.binder_qual);
                    FStar_Syntax_Syntax.binder_attrs =
                      (uu___2.FStar_Syntax_Syntax.binder_attrs)
                  }
              | uu___2 -> failwith "Not a renaming"))
let (subst_goal : FStar_Syntax_Syntax.subst_elt Prims.list -> goal -> goal) =
  fun subst ->
    fun goal1 ->
      let g = goal1.goal_ctx_uvar in
      let ctx_uvar =
        let uu___ = g in
        let uu___1 =
          FStar_TypeChecker_Env.rename_gamma subst
            g.FStar_Syntax_Syntax.ctx_uvar_gamma in
        let uu___2 =
          rename_binders subst g.FStar_Syntax_Syntax.ctx_uvar_binders in
        let uu___3 =
          FStar_Syntax_Subst.subst subst g.FStar_Syntax_Syntax.ctx_uvar_typ in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma = uu___1;
          FStar_Syntax_Syntax.ctx_uvar_binders = uu___2;
          FStar_Syntax_Syntax.ctx_uvar_typ = uu___3;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___.FStar_Syntax_Syntax.ctx_uvar_meta)
        } in
      let uu___ = goal1 in
      {
        goal_main_env = (uu___.goal_main_env);
        goal_ctx_uvar = ctx_uvar;
        opts = (uu___.opts);
        is_guard = (uu___.is_guard);
        label = (uu___.label)
      }
type guard_policy =
  | Goal 
  | SMT 
  | Force 
  | Drop 
let (uu___is_Goal : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | Goal -> true | uu___ -> false
let (uu___is_SMT : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | SMT -> true | uu___ -> false
let (uu___is_Force : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | Force -> true | uu___ -> false
let (uu___is_Drop : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | Drop -> true | uu___ -> false
type proofstate =
  {
  main_context: FStar_TypeChecker_Env.env ;
  all_implicits: FStar_TypeChecker_Common.implicits ;
  goals: goal Prims.list ;
  smt_goals: goal Prims.list ;
  depth: Prims.int ;
  __dump: proofstate -> Prims.string -> unit ;
  psc: FStar_TypeChecker_Cfg.psc ;
  entry_range: FStar_Range.range ;
  guard_policy: guard_policy ;
  freshness: Prims.int ;
  tac_verb_dbg: Prims.bool ;
  local_state: FStar_Syntax_Syntax.term FStar_Util.psmap ;
  urgency: Prims.int }
let (__proj__Mkproofstate__item__main_context :
  proofstate -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state; urgency;_} -> main_context
let (__proj__Mkproofstate__item__all_implicits :
  proofstate -> FStar_TypeChecker_Common.implicits) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state; urgency;_} -> all_implicits
let (__proj__Mkproofstate__item__goals : proofstate -> goal Prims.list) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state; urgency;_} -> goals
let (__proj__Mkproofstate__item__smt_goals : proofstate -> goal Prims.list) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state; urgency;_} -> smt_goals
let (__proj__Mkproofstate__item__depth : proofstate -> Prims.int) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state; urgency;_} -> depth
let (__proj__Mkproofstate__item____dump :
  proofstate -> proofstate -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state; urgency;_} -> __dump
let (__proj__Mkproofstate__item__psc :
  proofstate -> FStar_TypeChecker_Cfg.psc) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state; urgency;_} -> psc
let (__proj__Mkproofstate__item__entry_range :
  proofstate -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state; urgency;_} -> entry_range
let (__proj__Mkproofstate__item__guard_policy : proofstate -> guard_policy) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state; urgency;_} -> guard_policy1
let (__proj__Mkproofstate__item__freshness : proofstate -> Prims.int) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state; urgency;_} -> freshness
let (__proj__Mkproofstate__item__tac_verb_dbg : proofstate -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state; urgency;_} -> tac_verb_dbg
let (__proj__Mkproofstate__item__local_state :
  proofstate -> FStar_Syntax_Syntax.term FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state; urgency;_} -> local_state
let (__proj__Mkproofstate__item__urgency : proofstate -> Prims.int) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state; urgency;_} -> urgency
let (subst_proof_state :
  FStar_Syntax_Syntax.subst_t -> proofstate -> proofstate) =
  fun subst ->
    fun ps ->
      let uu___ = FStar_Options.tactic_raw_binders () in
      if uu___
      then ps
      else
        (let uu___2 = ps in
         let uu___3 = FStar_List.map (subst_goal subst) ps.goals in
         {
           main_context = (uu___2.main_context);
           all_implicits = (uu___2.all_implicits);
           goals = uu___3;
           smt_goals = (uu___2.smt_goals);
           depth = (uu___2.depth);
           __dump = (uu___2.__dump);
           psc = (uu___2.psc);
           entry_range = (uu___2.entry_range);
           guard_policy = (uu___2.guard_policy);
           freshness = (uu___2.freshness);
           tac_verb_dbg = (uu___2.tac_verb_dbg);
           local_state = (uu___2.local_state);
           urgency = (uu___2.urgency)
         })
let (decr_depth : proofstate -> proofstate) =
  fun ps ->
    let uu___ = ps in
    {
      main_context = (uu___.main_context);
      all_implicits = (uu___.all_implicits);
      goals = (uu___.goals);
      smt_goals = (uu___.smt_goals);
      depth = (ps.depth - Prims.int_one);
      __dump = (uu___.__dump);
      psc = (uu___.psc);
      entry_range = (uu___.entry_range);
      guard_policy = (uu___.guard_policy);
      freshness = (uu___.freshness);
      tac_verb_dbg = (uu___.tac_verb_dbg);
      local_state = (uu___.local_state);
      urgency = (uu___.urgency)
    }
let (incr_depth : proofstate -> proofstate) =
  fun ps ->
    let uu___ = ps in
    {
      main_context = (uu___.main_context);
      all_implicits = (uu___.all_implicits);
      goals = (uu___.goals);
      smt_goals = (uu___.smt_goals);
      depth = (ps.depth + Prims.int_one);
      __dump = (uu___.__dump);
      psc = (uu___.psc);
      entry_range = (uu___.entry_range);
      guard_policy = (uu___.guard_policy);
      freshness = (uu___.freshness);
      tac_verb_dbg = (uu___.tac_verb_dbg);
      local_state = (uu___.local_state);
      urgency = (uu___.urgency)
    }
let (set_ps_psc : FStar_TypeChecker_Cfg.psc -> proofstate -> proofstate) =
  fun psc ->
    fun ps ->
      let uu___ = ps in
      {
        main_context = (uu___.main_context);
        all_implicits = (uu___.all_implicits);
        goals = (uu___.goals);
        smt_goals = (uu___.smt_goals);
        depth = (uu___.depth);
        __dump = (uu___.__dump);
        psc;
        entry_range = (uu___.entry_range);
        guard_policy = (uu___.guard_policy);
        freshness = (uu___.freshness);
        tac_verb_dbg = (uu___.tac_verb_dbg);
        local_state = (uu___.local_state);
        urgency = (uu___.urgency)
      }
let (tracepoint_with_psc :
  FStar_TypeChecker_Cfg.psc -> proofstate -> Prims.bool) =
  fun psc ->
    fun ps ->
      (let uu___1 =
         (FStar_Options.tactic_trace ()) ||
           (let uu___2 = FStar_Options.tactic_trace_d () in
            ps.depth <= uu___2) in
       if uu___1
       then
         let ps1 = set_ps_psc psc ps in
         let subst = FStar_TypeChecker_Cfg.psc_subst ps1.psc in
         let uu___2 = subst_proof_state subst ps1 in
         ps1.__dump uu___2 "TRACE"
       else ());
      true
let (tracepoint : proofstate -> Prims.bool) =
  fun ps ->
    (let uu___1 =
       (FStar_Options.tactic_trace ()) ||
         (let uu___2 = FStar_Options.tactic_trace_d () in ps.depth <= uu___2) in
     if uu___1
     then
       let subst = FStar_TypeChecker_Cfg.psc_subst ps.psc in
       let uu___2 = subst_proof_state subst ps in ps.__dump uu___2 "TRACE"
     else ());
    true
let (set_proofstate_range : proofstate -> FStar_Range.range -> proofstate) =
  fun ps ->
    fun r ->
      let uu___ = ps in
      let uu___1 =
        let uu___2 = FStar_Range.def_range r in
        FStar_Range.set_def_range ps.entry_range uu___2 in
      {
        main_context = (uu___.main_context);
        all_implicits = (uu___.all_implicits);
        goals = (uu___.goals);
        smt_goals = (uu___.smt_goals);
        depth = (uu___.depth);
        __dump = (uu___.__dump);
        psc = (uu___.psc);
        entry_range = uu___1;
        guard_policy = (uu___.guard_policy);
        freshness = (uu___.freshness);
        tac_verb_dbg = (uu___.tac_verb_dbg);
        local_state = (uu___.local_state);
        urgency = (uu___.urgency)
      }
let (goals_of : proofstate -> goal Prims.list) = fun ps -> ps.goals
let (smt_goals_of : proofstate -> goal Prims.list) = fun ps -> ps.smt_goals
let (is_guard : goal -> Prims.bool) = fun g -> g.is_guard
let (get_label : goal -> Prims.string) = fun g -> g.label
let (set_label : Prims.string -> goal -> goal) =
  fun l ->
    fun g ->
      let uu___ = g in
      {
        goal_main_env = (uu___.goal_main_env);
        goal_ctx_uvar = (uu___.goal_ctx_uvar);
        opts = (uu___.opts);
        is_guard = (uu___.is_guard);
        label = l
      }
type direction =
  | TopDown 
  | BottomUp 
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee -> match projectee with | TopDown -> true | uu___ -> false
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee -> match projectee with | BottomUp -> true | uu___ -> false
type ctrl_flag =
  | Continue 
  | Skip 
  | Abort 
let (uu___is_Continue : ctrl_flag -> Prims.bool) =
  fun projectee -> match projectee with | Continue -> true | uu___ -> false
let (uu___is_Skip : ctrl_flag -> Prims.bool) =
  fun projectee -> match projectee with | Skip -> true | uu___ -> false
let (uu___is_Abort : ctrl_flag -> Prims.bool) =
  fun projectee -> match projectee with | Abort -> true | uu___ -> false
let (check_goal_solved' :
  goal -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun goal1 ->
    let uu___ =
      FStar_Syntax_Unionfind.find
        (goal1.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
    match uu___ with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (check_goal_solved : goal -> Prims.bool) =
  fun goal1 ->
    let uu___ = check_goal_solved' goal1 in FStar_Option.isSome uu___
let (get_phi :
  goal -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun g ->
    let uu___ =
      let uu___1 = goal_env g in
      let uu___2 = goal_type g in
      FStar_TypeChecker_Normalize.unfold_whnf uu___1 uu___2 in
    FStar_Syntax_Util.un_squash uu___
let (is_irrelevant : goal -> Prims.bool) =
  fun g -> let uu___ = get_phi g in FStar_Option.isSome uu___