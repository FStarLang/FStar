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
    let uu___244_62 = g.goal_main_env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___244_62.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___244_62.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___244_62.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma =
        ((g.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___244_62.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___244_62.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___244_62.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___244_62.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___244_62.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___244_62.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___244_62.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp =
        (uu___244_62.FStar_TypeChecker_Env.instantiate_imp);
      FStar_TypeChecker_Env.effects =
        (uu___244_62.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___244_62.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___244_62.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___244_62.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___244_62.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___244_62.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___244_62.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___244_62.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___244_62.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___244_62.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___244_62.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___244_62.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___244_62.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___244_62.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___244_62.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___244_62.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___244_62.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___244_62.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___244_62.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___244_62.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___244_62.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.proof_ns =
        (uu___244_62.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___244_62.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___244_62.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___244_62.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___244_62.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___244_62.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___244_62.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___244_62.FStar_TypeChecker_Env.dep_graph)
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
        let uu___245_99 = c  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___245_99.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (uu___245_99.FStar_Syntax_Syntax.ctx_uvar_gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___245_99.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = t;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___245_99.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___245_99.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___245_99.FStar_Syntax_Syntax.ctx_uvar_range)
        }  in
      let uu___246_100 = g  in
      {
        goal_main_env = (uu___246_100.goal_main_env);
        goal_ctx_uvar = c';
        opts = (uu___246_100.opts);
        is_guard = (uu___246_100.is_guard)
      }
  
let (goal_with_env : goal -> FStar_TypeChecker_Env.env -> goal) =
  fun g  ->
    fun env  ->
      let c = g.goal_ctx_uvar  in
      let c' =
        let uu___247_113 = c  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___247_113.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (env.FStar_TypeChecker_Env.gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___247_113.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ =
            (uu___247_113.FStar_Syntax_Syntax.ctx_uvar_typ);
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___247_113.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___247_113.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___247_113.FStar_Syntax_Syntax.ctx_uvar_range)
        }  in
      let uu___248_114 = g  in
      {
        goal_main_env = env;
        goal_ctx_uvar = c';
        opts = (uu___248_114.opts);
        is_guard = (uu___248_114.is_guard)
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
        let uu___249_151 = g  in
        let uu____152 =
          FStar_TypeChecker_Env.rename_gamma subst1
            g.FStar_Syntax_Syntax.ctx_uvar_gamma
           in
        let uu____155 =
          FStar_Syntax_Subst.subst subst1 g.FStar_Syntax_Syntax.ctx_uvar_typ
           in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___249_151.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma = uu____152;
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___249_151.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = uu____155;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___249_151.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___249_151.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___249_151.FStar_Syntax_Syntax.ctx_uvar_range)
        }  in
      let uu___250_158 = goal  in
      {
        goal_main_env = (uu___250_158.goal_main_env);
        goal_ctx_uvar = ctx_uvar;
        opts = (uu___250_158.opts);
        is_guard = (uu___250_158.is_guard)
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
  psc: FStar_TypeChecker_Normalize.psc ;
  entry_range: FStar_Range.range ;
  guard_policy: guard_policy ;
  freshness: Prims.int ;
  tac_verb_dbg: Prims.bool }
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
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__main_context
  
let (__proj__Mkproofstate__item__main_goal : proofstate -> goal) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__main_goal
  
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
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__all_implicits
  
let (__proj__Mkproofstate__item__goals : proofstate -> goal Prims.list) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__goals
  
let (__proj__Mkproofstate__item__smt_goals : proofstate -> goal Prims.list) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__smt_goals
  
let (__proj__Mkproofstate__item__depth : proofstate -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__depth
  
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
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname____dump
  
let (__proj__Mkproofstate__item__psc :
  proofstate -> FStar_TypeChecker_Normalize.psc) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__psc
  
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
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__entry_range
  
let (__proj__Mkproofstate__item__guard_policy : proofstate -> guard_policy) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__guard_policy
  
let (__proj__Mkproofstate__item__freshness : proofstate -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__freshness
  
let (__proj__Mkproofstate__item__tac_verb_dbg : proofstate -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__tac_verb_dbg
  
let (subst_proof_state :
  FStar_Syntax_Syntax.subst_t -> proofstate -> proofstate) =
  fun subst1  ->
    fun ps  ->
      let uu____613 = FStar_Options.tactic_raw_binders ()  in
      if uu____613
      then ps
      else
        (let uu___251_615 = ps  in
         let uu____616 = subst_goal subst1 ps.main_goal  in
         let uu____617 = FStar_List.map (subst_goal subst1) ps.goals  in
         {
           main_context = (uu___251_615.main_context);
           main_goal = uu____616;
           all_implicits = (uu___251_615.all_implicits);
           goals = uu____617;
           smt_goals = (uu___251_615.smt_goals);
           depth = (uu___251_615.depth);
           __dump = (uu___251_615.__dump);
           psc = (uu___251_615.psc);
           entry_range = (uu___251_615.entry_range);
           guard_policy = (uu___251_615.guard_policy);
           freshness = (uu___251_615.freshness);
           tac_verb_dbg = (uu___251_615.tac_verb_dbg)
         })
  
let (decr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___252_625 = ps  in
    {
      main_context = (uu___252_625.main_context);
      main_goal = (uu___252_625.main_goal);
      all_implicits = (uu___252_625.all_implicits);
      goals = (uu___252_625.goals);
      smt_goals = (uu___252_625.smt_goals);
      depth = (ps.depth - (Prims.parse_int "1"));
      __dump = (uu___252_625.__dump);
      psc = (uu___252_625.psc);
      entry_range = (uu___252_625.entry_range);
      guard_policy = (uu___252_625.guard_policy);
      freshness = (uu___252_625.freshness);
      tac_verb_dbg = (uu___252_625.tac_verb_dbg)
    }
  
let (incr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___253_631 = ps  in
    {
      main_context = (uu___253_631.main_context);
      main_goal = (uu___253_631.main_goal);
      all_implicits = (uu___253_631.all_implicits);
      goals = (uu___253_631.goals);
      smt_goals = (uu___253_631.smt_goals);
      depth = (ps.depth + (Prims.parse_int "1"));
      __dump = (uu___253_631.__dump);
      psc = (uu___253_631.psc);
      entry_range = (uu___253_631.entry_range);
      guard_policy = (uu___253_631.guard_policy);
      freshness = (uu___253_631.freshness);
      tac_verb_dbg = (uu___253_631.tac_verb_dbg)
    }
  
let (tracepoint : proofstate -> unit) =
  fun ps  ->
    let uu____637 =
      (FStar_Options.tactic_trace ()) ||
        (let uu____639 = FStar_Options.tactic_trace_d ()  in
         ps.depth <= uu____639)
       in
    if uu____637
    then
      let uu____640 =
        let uu____641 = FStar_TypeChecker_Normalize.psc_subst ps.psc  in
        subst_proof_state uu____641 ps  in
      ps.__dump uu____640 "TRACE"
    else ()
  
let (set_ps_psc :
  FStar_TypeChecker_Normalize.psc -> proofstate -> proofstate) =
  fun psc  ->
    fun ps  ->
      let uu___254_653 = ps  in
      {
        main_context = (uu___254_653.main_context);
        main_goal = (uu___254_653.main_goal);
        all_implicits = (uu___254_653.all_implicits);
        goals = (uu___254_653.goals);
        smt_goals = (uu___254_653.smt_goals);
        depth = (uu___254_653.depth);
        __dump = (uu___254_653.__dump);
        psc;
        entry_range = (uu___254_653.entry_range);
        guard_policy = (uu___254_653.guard_policy);
        freshness = (uu___254_653.freshness);
        tac_verb_dbg = (uu___254_653.tac_verb_dbg)
      }
  
let (set_proofstate_range : proofstate -> FStar_Range.range -> proofstate) =
  fun ps  ->
    fun r  ->
      let uu___255_664 = ps  in
      let uu____665 =
        let uu____666 = FStar_Range.def_range r  in
        FStar_Range.set_def_range ps.entry_range uu____666  in
      {
        main_context = (uu___255_664.main_context);
        main_goal = (uu___255_664.main_goal);
        all_implicits = (uu___255_664.all_implicits);
        goals = (uu___255_664.goals);
        smt_goals = (uu___255_664.smt_goals);
        depth = (uu___255_664.depth);
        __dump = (uu___255_664.__dump);
        psc = (uu___255_664.psc);
        entry_range = uu____665;
        guard_policy = (uu___255_664.guard_policy);
        freshness = (uu___255_664.freshness);
        tac_verb_dbg = (uu___255_664.tac_verb_dbg)
      }
  
type direction =
  | TopDown 
  | BottomUp 
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopDown  -> true | uu____672 -> false
  
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | BottomUp  -> true | uu____678 -> false
  