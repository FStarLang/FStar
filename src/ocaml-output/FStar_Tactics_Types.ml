open Prims
type goal =
  {
  goal_main_env: FStar_TypeChecker_Env.env ;
  goal_ctx_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  opts: FStar_Options.optionstate ;
  is_guard: Prims.bool }
let (__proj__Mkgoal__item__goal_main_env : goal -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { goal_main_env = __fname__goal_main_env;
        goal_ctx_uvar = __fname__goal_ctx_uvar; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__goal_main_env
  
let (__proj__Mkgoal__item__goal_ctx_uvar :
  goal -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  ->
    match projectee with
    | { goal_main_env = __fname__goal_main_env;
        goal_ctx_uvar = __fname__goal_ctx_uvar; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__goal_ctx_uvar
  
let (__proj__Mkgoal__item__opts : goal -> FStar_Options.optionstate) =
  fun projectee  ->
    match projectee with
    | { goal_main_env = __fname__goal_main_env;
        goal_ctx_uvar = __fname__goal_ctx_uvar; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__opts
  
let (__proj__Mkgoal__item__is_guard : goal -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { goal_main_env = __fname__goal_main_env;
        goal_ctx_uvar = __fname__goal_ctx_uvar; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__is_guard
  
let (goal_env : goal -> FStar_TypeChecker_Env.env) =
  fun g  ->
    let uu___251_62 = g.goal_main_env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___251_62.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___251_62.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___251_62.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma =
        ((g.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___251_62.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___251_62.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___251_62.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___251_62.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___251_62.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___251_62.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___251_62.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp =
        (uu___251_62.FStar_TypeChecker_Env.instantiate_imp);
      FStar_TypeChecker_Env.effects =
        (uu___251_62.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___251_62.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___251_62.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___251_62.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___251_62.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___251_62.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___251_62.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___251_62.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___251_62.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___251_62.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___251_62.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___251_62.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___251_62.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___251_62.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___251_62.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___251_62.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___251_62.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___251_62.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___251_62.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___251_62.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___251_62.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___251_62.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___251_62.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___251_62.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___251_62.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___251_62.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___251_62.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___251_62.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___251_62.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___251_62.FStar_TypeChecker_Env.nbe)
    }
  
let (goal_witness : goal -> FStar_Syntax_Syntax.term) =
  fun g  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uvar
         ((g.goal_ctx_uvar), ([], FStar_Syntax_Syntax.NoUseRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (goal_type : goal -> FStar_Syntax_Syntax.term) =
  fun g  -> (g.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ 
let (goal_with_type : goal -> FStar_Syntax_Syntax.term -> goal) =
  fun g  ->
    fun t  ->
      let c = g.goal_ctx_uvar  in
      let c' =
        let uu___252_99 = c  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___252_99.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (uu___252_99.FStar_Syntax_Syntax.ctx_uvar_gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___252_99.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = t;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___252_99.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___252_99.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___252_99.FStar_Syntax_Syntax.ctx_uvar_range)
        }  in
      let uu___253_100 = g  in
      {
        goal_main_env = (uu___253_100.goal_main_env);
        goal_ctx_uvar = c';
        opts = (uu___253_100.opts);
        is_guard = (uu___253_100.is_guard)
      }
  
let (goal_with_env : goal -> FStar_TypeChecker_Env.env -> goal) =
  fun g  ->
    fun env  ->
      let c = g.goal_ctx_uvar  in
      let c' =
        let uu___254_113 = c  in
        let uu____114 = FStar_TypeChecker_Env.all_binders env  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___254_113.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (env.FStar_TypeChecker_Env.gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders = uu____114;
          FStar_Syntax_Syntax.ctx_uvar_typ =
            (uu___254_113.FStar_Syntax_Syntax.ctx_uvar_typ);
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___254_113.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___254_113.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___254_113.FStar_Syntax_Syntax.ctx_uvar_range)
        }  in
      let uu___255_123 = g  in
      {
        goal_main_env = env;
        goal_ctx_uvar = c';
        opts = (uu___255_123.opts);
        is_guard = (uu___255_123.is_guard)
      }
  
let (mk_goal :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Options.optionstate -> Prims.bool -> goal)
  =
  fun env  ->
    fun u  ->
      fun o  ->
        fun b  ->
          { goal_main_env = env; goal_ctx_uvar = u; opts = o; is_guard = b }
  
let (subst_goal : FStar_Syntax_Syntax.subst_elt Prims.list -> goal -> goal) =
  fun subst1  ->
    fun goal  ->
      let g = goal.goal_ctx_uvar  in
      let ctx_uvar =
        let uu___256_160 = g  in
        let uu____161 =
          FStar_TypeChecker_Env.rename_gamma subst1
            g.FStar_Syntax_Syntax.ctx_uvar_gamma
           in
        let uu____164 =
          FStar_Syntax_Subst.subst subst1 g.FStar_Syntax_Syntax.ctx_uvar_typ
           in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___256_160.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma = uu____161;
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___256_160.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = uu____164;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___256_160.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___256_160.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___256_160.FStar_Syntax_Syntax.ctx_uvar_range)
        }  in
      let uu___257_167 = goal  in
      {
        goal_main_env = (uu___257_167.goal_main_env);
        goal_ctx_uvar = ctx_uvar;
        opts = (uu___257_167.opts);
        is_guard = (uu___257_167.is_guard)
      }
  
type guard_policy =
  | Goal 
  | SMT 
  | Force 
  | Drop 
let (uu___is_Goal : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Goal  -> true | uu____173 -> false 
let (uu___is_SMT : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | SMT  -> true | uu____179 -> false 
let (uu___is_Force : guard_policy -> Prims.bool) =
  fun projectee  ->
    match projectee with | Force  -> true | uu____185 -> false
  
let (uu___is_Drop : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Drop  -> true | uu____191 -> false 
type proofstate =
  {
  main_context: FStar_TypeChecker_Env.env ;
  main_goal: goal ;
  all_implicits: FStar_TypeChecker_Env.implicits ;
  goals: goal Prims.list ;
  smt_goals: goal Prims.list ;
  depth: Prims.int ;
  __dump: proofstate -> Prims.string -> unit ;
  psc: FStar_TypeChecker_Cfg.psc ;
  entry_range: FStar_Range.range ;
  guard_policy: guard_policy ;
  freshness: Prims.int ;
  tac_verb_dbg: Prims.bool ;
  local_state: FStar_Syntax_Syntax.term FStar_Util.psmap }
let (__proj__Mkproofstate__item__main_context :
  proofstate -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;
        local_state = __fname__local_state;_} -> __fname__main_context
  
let (__proj__Mkproofstate__item__main_goal : proofstate -> goal) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;
        local_state = __fname__local_state;_} -> __fname__main_goal
  
let (__proj__Mkproofstate__item__all_implicits :
  proofstate -> FStar_TypeChecker_Env.implicits) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;
        local_state = __fname__local_state;_} -> __fname__all_implicits
  
let (__proj__Mkproofstate__item__goals : proofstate -> goal Prims.list) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;
        local_state = __fname__local_state;_} -> __fname__goals
  
let (__proj__Mkproofstate__item__smt_goals : proofstate -> goal Prims.list) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;
        local_state = __fname__local_state;_} -> __fname__smt_goals
  
let (__proj__Mkproofstate__item__depth : proofstate -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;
        local_state = __fname__local_state;_} -> __fname__depth
  
let (__proj__Mkproofstate__item____dump :
  proofstate -> proofstate -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;
        local_state = __fname__local_state;_} -> __fname____dump
  
let (__proj__Mkproofstate__item__psc :
  proofstate -> FStar_TypeChecker_Cfg.psc) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;
        local_state = __fname__local_state;_} -> __fname__psc
  
let (__proj__Mkproofstate__item__entry_range :
  proofstate -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;
        local_state = __fname__local_state;_} -> __fname__entry_range
  
let (__proj__Mkproofstate__item__guard_policy : proofstate -> guard_policy) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;
        local_state = __fname__local_state;_} -> __fname__guard_policy
  
let (__proj__Mkproofstate__item__freshness : proofstate -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;
        local_state = __fname__local_state;_} -> __fname__freshness
  
let (__proj__Mkproofstate__item__tac_verb_dbg : proofstate -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;
        local_state = __fname__local_state;_} -> __fname__tac_verb_dbg
  
let (__proj__Mkproofstate__item__local_state :
  proofstate -> FStar_Syntax_Syntax.term FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;
        local_state = __fname__local_state;_} -> __fname__local_state
  
let (subst_proof_state :
  FStar_Syntax_Syntax.subst_t -> proofstate -> proofstate) =
  fun subst1  ->
    fun ps  ->
      let uu____699 = FStar_Options.tactic_raw_binders ()  in
      if uu____699
      then ps
      else
        (let uu___258_701 = ps  in
         let uu____702 = subst_goal subst1 ps.main_goal  in
         let uu____703 = FStar_List.map (subst_goal subst1) ps.goals  in
         {
           main_context = (uu___258_701.main_context);
           main_goal = uu____702;
           all_implicits = (uu___258_701.all_implicits);
           goals = uu____703;
           smt_goals = (uu___258_701.smt_goals);
           depth = (uu___258_701.depth);
           __dump = (uu___258_701.__dump);
           psc = (uu___258_701.psc);
           entry_range = (uu___258_701.entry_range);
           guard_policy = (uu___258_701.guard_policy);
           freshness = (uu___258_701.freshness);
           tac_verb_dbg = (uu___258_701.tac_verb_dbg);
           local_state = (uu___258_701.local_state)
         })
  
let (decr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___259_711 = ps  in
    {
      main_context = (uu___259_711.main_context);
      main_goal = (uu___259_711.main_goal);
      all_implicits = (uu___259_711.all_implicits);
      goals = (uu___259_711.goals);
      smt_goals = (uu___259_711.smt_goals);
      depth = (ps.depth - (Prims.parse_int "1"));
      __dump = (uu___259_711.__dump);
      psc = (uu___259_711.psc);
      entry_range = (uu___259_711.entry_range);
      guard_policy = (uu___259_711.guard_policy);
      freshness = (uu___259_711.freshness);
      tac_verb_dbg = (uu___259_711.tac_verb_dbg);
      local_state = (uu___259_711.local_state)
    }
  
let (incr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___260_717 = ps  in
    {
      main_context = (uu___260_717.main_context);
      main_goal = (uu___260_717.main_goal);
      all_implicits = (uu___260_717.all_implicits);
      goals = (uu___260_717.goals);
      smt_goals = (uu___260_717.smt_goals);
      depth = (ps.depth + (Prims.parse_int "1"));
      __dump = (uu___260_717.__dump);
      psc = (uu___260_717.psc);
      entry_range = (uu___260_717.entry_range);
      guard_policy = (uu___260_717.guard_policy);
      freshness = (uu___260_717.freshness);
      tac_verb_dbg = (uu___260_717.tac_verb_dbg);
      local_state = (uu___260_717.local_state)
    }
  
let (tracepoint : proofstate -> unit) =
  fun ps  ->
    let uu____723 =
      (FStar_Options.tactic_trace ()) ||
        (let uu____725 = FStar_Options.tactic_trace_d ()  in
         ps.depth <= uu____725)
       in
    if uu____723
    then
      let uu____726 =
        let uu____727 = FStar_TypeChecker_Cfg.psc_subst ps.psc  in
        subst_proof_state uu____727 ps  in
      ps.__dump uu____726 "TRACE"
    else ()
  
let (set_ps_psc : FStar_TypeChecker_Cfg.psc -> proofstate -> proofstate) =
  fun psc  ->
    fun ps  ->
      let uu___261_739 = ps  in
      {
        main_context = (uu___261_739.main_context);
        main_goal = (uu___261_739.main_goal);
        all_implicits = (uu___261_739.all_implicits);
        goals = (uu___261_739.goals);
        smt_goals = (uu___261_739.smt_goals);
        depth = (uu___261_739.depth);
        __dump = (uu___261_739.__dump);
        psc;
        entry_range = (uu___261_739.entry_range);
        guard_policy = (uu___261_739.guard_policy);
        freshness = (uu___261_739.freshness);
        tac_verb_dbg = (uu___261_739.tac_verb_dbg);
        local_state = (uu___261_739.local_state)
      }
  
let (set_proofstate_range : proofstate -> FStar_Range.range -> proofstate) =
  fun ps  ->
    fun r  ->
      let uu___262_750 = ps  in
      let uu____751 =
        let uu____752 = FStar_Range.def_range r  in
        FStar_Range.set_def_range ps.entry_range uu____752  in
      {
        main_context = (uu___262_750.main_context);
        main_goal = (uu___262_750.main_goal);
        all_implicits = (uu___262_750.all_implicits);
        goals = (uu___262_750.goals);
        smt_goals = (uu___262_750.smt_goals);
        depth = (uu___262_750.depth);
        __dump = (uu___262_750.__dump);
        psc = (uu___262_750.psc);
        entry_range = uu____751;
        guard_policy = (uu___262_750.guard_policy);
        freshness = (uu___262_750.freshness);
        tac_verb_dbg = (uu___262_750.tac_verb_dbg);
        local_state = (uu___262_750.local_state)
      }
  
let (goals_of : proofstate -> goal Prims.list) = fun ps  -> ps.goals 
let (smt_goals_of : proofstate -> goal Prims.list) = fun ps  -> ps.smt_goals 
let (is_guard : goal -> Prims.bool) = fun g  -> g.is_guard 
type direction =
  | TopDown 
  | BottomUp 
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopDown  -> true | uu____781 -> false
  
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | BottomUp  -> true | uu____787 -> false
  