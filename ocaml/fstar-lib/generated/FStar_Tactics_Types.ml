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
  entry_range: FStar_Compiler_Range_Type.range ;
  guard_policy: guard_policy ;
  freshness: Prims.int ;
  tac_verb_dbg: Prims.bool ;
  local_state: FStar_Syntax_Syntax.term FStar_Compiler_Util.psmap ;
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
  proofstate -> FStar_Compiler_Range_Type.range) =
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
  proofstate -> FStar_Syntax_Syntax.term FStar_Compiler_Util.psmap) =
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
let (goal_env : goal -> FStar_TypeChecker_Env.env) = fun g -> g.goal_main_env
let (goal_witness : goal -> FStar_Syntax_Syntax.term) =
  fun g ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uvar
         ((g.goal_ctx_uvar), ([], FStar_Syntax_Syntax.NoUseRange)))
      FStar_Compiler_Range_Type.dummyRange
let (goal_type : goal -> FStar_Syntax_Syntax.term) =
  fun g -> FStar_Syntax_Util.ctx_uvar_typ g.goal_ctx_uvar
let (goal_with_env : goal -> FStar_TypeChecker_Env.env -> goal) =
  fun g ->
    fun env ->
      let c = g.goal_ctx_uvar in
      let c' =
        let uu___ = FStar_TypeChecker_Env.all_binders env in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (c.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (env.FStar_TypeChecker_Env.gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders = uu___;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (c.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (c.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (c.FStar_Syntax_Syntax.ctx_uvar_meta)
        } in
      {
        goal_main_env = env;
        goal_ctx_uvar = c';
        opts = (g.opts);
        is_guard = (g.is_guard);
        label = (g.label)
      }
let (goal_of_ctx_uvar : goal -> FStar_Syntax_Syntax.ctx_uvar -> goal) =
  fun g ->
    fun ctx_u ->
      {
        goal_main_env = (g.goal_main_env);
        goal_ctx_uvar = ctx_u;
        opts = (g.opts);
        is_guard = (g.is_guard);
        label = (g.label)
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
          typ.FStar_Syntax_Syntax.pos env typ FStar_Syntax_Syntax.Strict
          FStar_Pervasives_Native.None in
      match uu___ with
      | (u, ctx_uvars, g_u) ->
          let uu___1 = FStar_Compiler_List.hd ctx_uvars in
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
        {
          FStar_TypeChecker_Env.solver = (env.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range = (env.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (env.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            ((i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (env.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (env.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules = (env.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (env.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab = (env.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab = (env.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.instantiate_imp =
            (env.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects = (env.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (env.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs = (env.FStar_TypeChecker_Env.letrecs);
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
          FStar_TypeChecker_Env.phase1 = (env.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard =
            (env.FStar_TypeChecker_Env.failhard);
          FStar_TypeChecker_Env.nosynth = (env.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (env.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.intactics =
            (env.FStar_TypeChecker_Env.intactics);
          FStar_TypeChecker_Env.tc_term = (env.FStar_TypeChecker_Env.tc_term);
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
          FStar_TypeChecker_Env.splice = (env.FStar_TypeChecker_Env.splice);
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
          FStar_TypeChecker_Env.core_check =
            (env.FStar_TypeChecker_Env.core_check)
        } i.FStar_TypeChecker_Common.imp_uvar uu___ false
        i.FStar_TypeChecker_Common.imp_reason
let (decr_depth : proofstate -> proofstate) =
  fun ps ->
    {
      main_context = (ps.main_context);
      all_implicits = (ps.all_implicits);
      goals = (ps.goals);
      smt_goals = (ps.smt_goals);
      depth = (ps.depth - Prims.int_one);
      __dump = (ps.__dump);
      psc = (ps.psc);
      entry_range = (ps.entry_range);
      guard_policy = (ps.guard_policy);
      freshness = (ps.freshness);
      tac_verb_dbg = (ps.tac_verb_dbg);
      local_state = (ps.local_state);
      urgency = (ps.urgency)
    }
let (incr_depth : proofstate -> proofstate) =
  fun ps ->
    {
      main_context = (ps.main_context);
      all_implicits = (ps.all_implicits);
      goals = (ps.goals);
      smt_goals = (ps.smt_goals);
      depth = (ps.depth + Prims.int_one);
      __dump = (ps.__dump);
      psc = (ps.psc);
      entry_range = (ps.entry_range);
      guard_policy = (ps.guard_policy);
      freshness = (ps.freshness);
      tac_verb_dbg = (ps.tac_verb_dbg);
      local_state = (ps.local_state);
      urgency = (ps.urgency)
    }
let (set_ps_psc : FStar_TypeChecker_Cfg.psc -> proofstate -> proofstate) =
  fun psc ->
    fun ps ->
      {
        main_context = (ps.main_context);
        all_implicits = (ps.all_implicits);
        goals = (ps.goals);
        smt_goals = (ps.smt_goals);
        depth = (ps.depth);
        __dump = (ps.__dump);
        psc;
        entry_range = (ps.entry_range);
        guard_policy = (ps.guard_policy);
        freshness = (ps.freshness);
        tac_verb_dbg = (ps.tac_verb_dbg);
        local_state = (ps.local_state);
        urgency = (ps.urgency)
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
       then let ps1 = set_ps_psc psc ps in ps1.__dump ps1 "TRACE"
       else ());
      true
let (tracepoint : proofstate -> Prims.bool) =
  fun ps ->
    (let uu___1 =
       (FStar_Options.tactic_trace ()) ||
         (let uu___2 = FStar_Options.tactic_trace_d () in ps.depth <= uu___2) in
     if uu___1 then ps.__dump ps "TRACE" else ());
    true
let (set_proofstate_range :
  proofstate -> FStar_Compiler_Range_Type.range -> proofstate) =
  fun ps ->
    fun r ->
      let uu___ =
        let uu___1 = FStar_Compiler_Range_Type.def_range r in
        FStar_Compiler_Range_Type.set_def_range ps.entry_range uu___1 in
      {
        main_context = (ps.main_context);
        all_implicits = (ps.all_implicits);
        goals = (ps.goals);
        smt_goals = (ps.smt_goals);
        depth = (ps.depth);
        __dump = (ps.__dump);
        psc = (ps.psc);
        entry_range = uu___;
        guard_policy = (ps.guard_policy);
        freshness = (ps.freshness);
        tac_verb_dbg = (ps.tac_verb_dbg);
        local_state = (ps.local_state);
        urgency = (ps.urgency)
      }
let (goals_of : proofstate -> goal Prims.list) = fun ps -> ps.goals
let (smt_goals_of : proofstate -> goal Prims.list) = fun ps -> ps.smt_goals
let (is_guard : goal -> Prims.bool) = fun g -> g.is_guard
let (get_label : goal -> Prims.string) = fun g -> g.label
let (set_label : Prims.string -> goal -> goal) =
  fun l ->
    fun g ->
      {
        goal_main_env = (g.goal_main_env);
        goal_ctx_uvar = (g.goal_ctx_uvar);
        opts = (g.opts);
        is_guard = (g.is_guard);
        label = l
      }
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
type direction =
  | TopDown 
  | BottomUp 
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee -> match projectee with | TopDown -> true | uu___ -> false
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee -> match projectee with | BottomUp -> true | uu___ -> false
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
    let uu___ = check_goal_solved' goal1 in
    FStar_Compiler_Option.isSome uu___
let (get_phi :
  goal -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun g ->
    let uu___ =
      let uu___1 = goal_env g in
      let uu___2 = goal_type g in
      FStar_TypeChecker_Normalize.unfold_whnf uu___1 uu___2 in
    FStar_Syntax_Util.un_squash uu___
let (is_irrelevant : goal -> Prims.bool) =
  fun g -> let uu___ = get_phi g in FStar_Compiler_Option.isSome uu___
type unfold_side =
  | Left 
  | Right 
  | Both 
  | Neither 
let (uu___is_Left : unfold_side -> Prims.bool) =
  fun projectee -> match projectee with | Left -> true | uu___ -> false
let (uu___is_Right : unfold_side -> Prims.bool) =
  fun projectee -> match projectee with | Right -> true | uu___ -> false
let (uu___is_Both : unfold_side -> Prims.bool) =
  fun projectee -> match projectee with | Both -> true | uu___ -> false
let (uu___is_Neither : unfold_side -> Prims.bool) =
  fun projectee -> match projectee with | Neither -> true | uu___ -> false
type tot_or_ghost =
  | E_Total 
  | E_Ghost 
let (uu___is_E_Total : tot_or_ghost -> Prims.bool) =
  fun projectee -> match projectee with | E_Total -> true | uu___ -> false
let (uu___is_E_Ghost : tot_or_ghost -> Prims.bool) =
  fun projectee -> match projectee with | E_Ghost -> true | uu___ -> false
type ('g, 't0, 't1) subtyping_token = unit
type ('g, 't0, 't1) equiv_token = unit
type ('g, 'e, 'c) typing_token = unit
type ('g, 'sc, 't, 'pats) match_complete_token = unit
type issues = FStar_Issue.issue Prims.list