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
    let uu___250_62 = g.goal_main_env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___250_62.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___250_62.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___250_62.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma =
        ((g.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___250_62.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___250_62.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___250_62.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___250_62.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___250_62.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___250_62.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___250_62.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp =
        (uu___250_62.FStar_TypeChecker_Env.instantiate_imp);
      FStar_TypeChecker_Env.effects =
        (uu___250_62.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___250_62.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___250_62.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___250_62.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___250_62.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___250_62.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___250_62.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___250_62.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___250_62.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___250_62.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___250_62.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___250_62.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___250_62.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___250_62.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___250_62.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___250_62.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___250_62.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___250_62.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___250_62.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___250_62.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___250_62.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.proof_ns =
        (uu___250_62.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___250_62.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___250_62.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___250_62.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___250_62.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___250_62.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___250_62.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___250_62.FStar_TypeChecker_Env.dep_graph);
      FStar_TypeChecker_Env.nbe = (uu___250_62.FStar_TypeChecker_Env.nbe)
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
        let uu___251_99 = c  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___251_99.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (uu___251_99.FStar_Syntax_Syntax.ctx_uvar_gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___251_99.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = t;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___251_99.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___251_99.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___251_99.FStar_Syntax_Syntax.ctx_uvar_range)
        }  in
      let uu___252_100 = g  in
      {
        goal_main_env = (uu___252_100.goal_main_env);
        goal_ctx_uvar = c';
        opts = (uu___252_100.opts);
        is_guard = (uu___252_100.is_guard)
      }
  
let (goal_with_env : goal -> FStar_TypeChecker_Env.env -> goal) =
  fun g  ->
    fun env  ->
      let c = g.goal_ctx_uvar  in
      let c' =
        let uu___253_113 = c  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___253_113.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (env.FStar_TypeChecker_Env.gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___253_113.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ =
            (uu___253_113.FStar_Syntax_Syntax.ctx_uvar_typ);
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___253_113.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___253_113.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___253_113.FStar_Syntax_Syntax.ctx_uvar_range)
        }  in
      let uu___254_114 = g  in
      {
        goal_main_env = env;
        goal_ctx_uvar = c';
        opts = (uu___254_114.opts);
        is_guard = (uu___254_114.is_guard)
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
        let uu___255_151 = g  in
        let uu____152 =
          FStar_TypeChecker_Env.rename_gamma subst1
            g.FStar_Syntax_Syntax.ctx_uvar_gamma
           in
        let uu____155 =
          FStar_Syntax_Subst.subst subst1 g.FStar_Syntax_Syntax.ctx_uvar_typ
           in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___255_151.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma = uu____152;
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___255_151.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = uu____155;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___255_151.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___255_151.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___255_151.FStar_Syntax_Syntax.ctx_uvar_range)
        }  in
      let uu___256_158 = goal  in
      {
        goal_main_env = (uu___256_158.goal_main_env);
        goal_ctx_uvar = ctx_uvar;
        opts = (uu___256_158.opts);
        is_guard = (uu___256_158.is_guard)
      }
  
type guard_policy =
  | Goal 
  | SMT 
  | Force 
  | Drop 
let (uu___is_Goal : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Goal  -> true | uu____164 -> false 
let (uu___is_SMT : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | SMT  -> true | uu____170 -> false 
let (uu___is_Force : guard_policy -> Prims.bool) =
  fun projectee  ->
    match projectee with | Force  -> true | uu____176 -> false
  
let (uu___is_Drop : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Drop  -> true | uu____182 -> false 
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
      let uu____690 = FStar_Options.tactic_raw_binders ()  in
      if uu____690
      then ps
      else
        (let uu___257_692 = ps  in
         let uu____693 = subst_goal subst1 ps.main_goal  in
         let uu____694 = FStar_List.map (subst_goal subst1) ps.goals  in
         {
           main_context = (uu___257_692.main_context);
           main_goal = uu____693;
           all_implicits = (uu___257_692.all_implicits);
           goals = uu____694;
           smt_goals = (uu___257_692.smt_goals);
           depth = (uu___257_692.depth);
           __dump = (uu___257_692.__dump);
           psc = (uu___257_692.psc);
           entry_range = (uu___257_692.entry_range);
           guard_policy = (uu___257_692.guard_policy);
           freshness = (uu___257_692.freshness);
           tac_verb_dbg = (uu___257_692.tac_verb_dbg);
           local_state = (uu___257_692.local_state)
         })
  
let (decr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___258_702 = ps  in
    {
      main_context = (uu___258_702.main_context);
      main_goal = (uu___258_702.main_goal);
      all_implicits = (uu___258_702.all_implicits);
      goals = (uu___258_702.goals);
      smt_goals = (uu___258_702.smt_goals);
      depth = (ps.depth - (Prims.parse_int "1"));
      __dump = (uu___258_702.__dump);
      psc = (uu___258_702.psc);
      entry_range = (uu___258_702.entry_range);
      guard_policy = (uu___258_702.guard_policy);
      freshness = (uu___258_702.freshness);
      tac_verb_dbg = (uu___258_702.tac_verb_dbg);
      local_state = (uu___258_702.local_state)
    }
  
let (incr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___259_708 = ps  in
    {
      main_context = (uu___259_708.main_context);
      main_goal = (uu___259_708.main_goal);
      all_implicits = (uu___259_708.all_implicits);
      goals = (uu___259_708.goals);
      smt_goals = (uu___259_708.smt_goals);
      depth = (ps.depth + (Prims.parse_int "1"));
      __dump = (uu___259_708.__dump);
      psc = (uu___259_708.psc);
      entry_range = (uu___259_708.entry_range);
      guard_policy = (uu___259_708.guard_policy);
      freshness = (uu___259_708.freshness);
      tac_verb_dbg = (uu___259_708.tac_verb_dbg);
      local_state = (uu___259_708.local_state)
    }
  
let (tracepoint : proofstate -> unit) =
  fun ps  ->
    let uu____714 =
      (FStar_Options.tactic_trace ()) ||
        (let uu____716 = FStar_Options.tactic_trace_d ()  in
         ps.depth <= uu____716)
       in
    if uu____714
    then
      let uu____717 =
        let uu____718 = FStar_TypeChecker_Cfg.psc_subst ps.psc  in
        subst_proof_state uu____718 ps  in
      ps.__dump uu____717 "TRACE"
    else ()
  
let (set_ps_psc : FStar_TypeChecker_Cfg.psc -> proofstate -> proofstate) =
  fun psc  ->
    fun ps  ->
      let uu___260_730 = ps  in
      {
        main_context = (uu___260_730.main_context);
        main_goal = (uu___260_730.main_goal);
        all_implicits = (uu___260_730.all_implicits);
        goals = (uu___260_730.goals);
        smt_goals = (uu___260_730.smt_goals);
        depth = (uu___260_730.depth);
        __dump = (uu___260_730.__dump);
        psc;
        entry_range = (uu___260_730.entry_range);
        guard_policy = (uu___260_730.guard_policy);
        freshness = (uu___260_730.freshness);
        tac_verb_dbg = (uu___260_730.tac_verb_dbg);
        local_state = (uu___260_730.local_state)
      }
  
let (set_proofstate_range : proofstate -> FStar_Range.range -> proofstate) =
  fun ps  ->
    fun r  ->
      let uu___261_741 = ps  in
      let uu____742 =
        let uu____743 = FStar_Range.def_range r  in
        FStar_Range.set_def_range ps.entry_range uu____743  in
      {
        main_context = (uu___261_741.main_context);
        main_goal = (uu___261_741.main_goal);
        all_implicits = (uu___261_741.all_implicits);
        goals = (uu___261_741.goals);
        smt_goals = (uu___261_741.smt_goals);
        depth = (uu___261_741.depth);
        __dump = (uu___261_741.__dump);
        psc = (uu___261_741.psc);
        entry_range = uu____742;
        guard_policy = (uu___261_741.guard_policy);
        freshness = (uu___261_741.freshness);
        tac_verb_dbg = (uu___261_741.tac_verb_dbg);
        local_state = (uu___261_741.local_state)
      }
  
let (goals : proofstate -> goal Prims.list) = fun ps  -> ps.goals 
let (smtgoals : proofstate -> goal Prims.list) = fun ps  -> ps.smt_goals 
type direction =
  | TopDown 
  | BottomUp 
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopDown  -> true | uu____767 -> false
  
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | BottomUp  -> true | uu____773 -> false
  