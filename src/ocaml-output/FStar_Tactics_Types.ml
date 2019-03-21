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
  fun projectee  ->
    match projectee with
    | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} ->
        goal_main_env
  
let (__proj__Mkgoal__item__goal_ctx_uvar :
  goal -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  ->
    match projectee with
    | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} ->
        goal_ctx_uvar
  
let (__proj__Mkgoal__item__opts : goal -> FStar_Options.optionstate) =
  fun projectee  ->
    match projectee with
    | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} -> opts
  
let (__proj__Mkgoal__item__is_guard : goal -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} -> is_guard
  
let (__proj__Mkgoal__item__label : goal -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} -> label
  
let (goal_env : goal -> FStar_TypeChecker_Env.env) =
  fun g  ->
    let uu___601_59700 = g.goal_main_env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___601_59700.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range =
        (uu___601_59700.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___601_59700.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma =
        ((g.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___601_59700.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___601_59700.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___601_59700.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___601_59700.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___601_59700.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___601_59700.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___601_59700.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp =
        (uu___601_59700.FStar_TypeChecker_Env.instantiate_imp);
      FStar_TypeChecker_Env.effects =
        (uu___601_59700.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___601_59700.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___601_59700.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___601_59700.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___601_59700.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___601_59700.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___601_59700.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit =
        (uu___601_59700.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___601_59700.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___601_59700.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___601_59700.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___601_59700.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___601_59700.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___601_59700.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___601_59700.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___601_59700.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___601_59700.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___601_59700.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___601_59700.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___601_59700.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___601_59700.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___601_59700.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___601_59700.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___601_59700.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___601_59700.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.postprocess =
        (uu___601_59700.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___601_59700.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___601_59700.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___601_59700.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv =
        (uu___601_59700.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___601_59700.FStar_TypeChecker_Env.nbe)
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
        let uu___608_59740 = c  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___608_59740.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (uu___608_59740.FStar_Syntax_Syntax.ctx_uvar_gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___608_59740.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = t;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___608_59740.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___608_59740.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___608_59740.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___608_59740.FStar_Syntax_Syntax.ctx_uvar_meta)
        }  in
      let uu___611_59741 = g  in
      {
        goal_main_env = (uu___611_59741.goal_main_env);
        goal_ctx_uvar = c';
        opts = (uu___611_59741.opts);
        is_guard = (uu___611_59741.is_guard);
        label = (uu___611_59741.label)
      }
  
let (goal_with_env : goal -> FStar_TypeChecker_Env.env -> goal) =
  fun g  ->
    fun env  ->
      let c = g.goal_ctx_uvar  in
      let c' =
        let uu___616_59755 = c  in
        let uu____59756 = FStar_TypeChecker_Env.all_binders env  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___616_59755.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (env.FStar_TypeChecker_Env.gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders = uu____59756;
          FStar_Syntax_Syntax.ctx_uvar_typ =
            (uu___616_59755.FStar_Syntax_Syntax.ctx_uvar_typ);
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___616_59755.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___616_59755.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___616_59755.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___616_59755.FStar_Syntax_Syntax.ctx_uvar_meta)
        }  in
      let uu___619_59765 = g  in
      {
        goal_main_env = env;
        goal_ctx_uvar = c';
        opts = (uu___619_59765.opts);
        is_guard = (uu___619_59765.is_guard);
        label = (uu___619_59765.label)
      }
  
let (mk_goal :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Options.optionstate -> Prims.bool -> Prims.string -> goal)
  =
  fun env  ->
    fun u  ->
      fun o  ->
        fun b  ->
          fun l  ->
            {
              goal_main_env = env;
              goal_ctx_uvar = u;
              opts = o;
              is_guard = b;
              label = l
            }
  
let (subst_goal : FStar_Syntax_Syntax.subst_elt Prims.list -> goal -> goal) =
  fun subst1  ->
    fun goal  ->
      let g = goal.goal_ctx_uvar  in
      let ctx_uvar =
        let uu___629_59813 = g  in
        let uu____59814 =
          FStar_TypeChecker_Env.rename_gamma subst1
            g.FStar_Syntax_Syntax.ctx_uvar_gamma
           in
        let uu____59817 =
          FStar_Syntax_Subst.subst subst1 g.FStar_Syntax_Syntax.ctx_uvar_typ
           in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___629_59813.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma = uu____59814;
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___629_59813.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = uu____59817;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___629_59813.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___629_59813.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___629_59813.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___629_59813.FStar_Syntax_Syntax.ctx_uvar_meta)
        }  in
      let uu___632_59820 = goal  in
      {
        goal_main_env = (uu___632_59820.goal_main_env);
        goal_ctx_uvar = ctx_uvar;
        opts = (uu___632_59820.opts);
        is_guard = (uu___632_59820.is_guard);
        label = (uu___632_59820.label)
      }
  
type guard_policy =
  | Goal 
  | SMT 
  | Force 
  | Drop 
let (uu___is_Goal : guard_policy -> Prims.bool) =
  fun projectee  ->
    match projectee with | Goal  -> true | uu____59830 -> false
  
let (uu___is_SMT : guard_policy -> Prims.bool) =
  fun projectee  ->
    match projectee with | SMT  -> true | uu____59841 -> false
  
let (uu___is_Force : guard_policy -> Prims.bool) =
  fun projectee  ->
    match projectee with | Force  -> true | uu____59852 -> false
  
let (uu___is_Drop : guard_policy -> Prims.bool) =
  fun projectee  ->
    match projectee with | Drop  -> true | uu____59863 -> false
  
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
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> main_context
  
let (__proj__Mkproofstate__item__main_goal : proofstate -> goal) =
  fun projectee  ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> main_goal
  
let (__proj__Mkproofstate__item__all_implicits :
  proofstate -> FStar_TypeChecker_Env.implicits) =
  fun projectee  ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> all_implicits
  
let (__proj__Mkproofstate__item__goals : proofstate -> goal Prims.list) =
  fun projectee  ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> goals
  
let (__proj__Mkproofstate__item__smt_goals : proofstate -> goal Prims.list) =
  fun projectee  ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> smt_goals
  
let (__proj__Mkproofstate__item__depth : proofstate -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> depth
  
let (__proj__Mkproofstate__item____dump :
  proofstate -> proofstate -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> __dump
  
let (__proj__Mkproofstate__item__psc :
  proofstate -> FStar_TypeChecker_Cfg.psc) =
  fun projectee  ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> psc
  
let (__proj__Mkproofstate__item__entry_range :
  proofstate -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> entry_range
  
let (__proj__Mkproofstate__item__guard_policy : proofstate -> guard_policy) =
  fun projectee  ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> guard_policy
  
let (__proj__Mkproofstate__item__freshness : proofstate -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> freshness
  
let (__proj__Mkproofstate__item__tac_verb_dbg : proofstate -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> tac_verb_dbg
  
let (__proj__Mkproofstate__item__local_state :
  proofstate -> FStar_Syntax_Syntax.term FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> local_state
  
let (subst_proof_state :
  FStar_Syntax_Syntax.subst_t -> proofstate -> proofstate) =
  fun subst1  ->
    fun ps  ->
      let uu____60450 = FStar_Options.tactic_raw_binders ()  in
      if uu____60450
      then ps
      else
        (let uu___676_60455 = ps  in
         let uu____60456 = subst_goal subst1 ps.main_goal  in
         let uu____60457 = FStar_List.map (subst_goal subst1) ps.goals  in
         {
           main_context = (uu___676_60455.main_context);
           main_goal = uu____60456;
           all_implicits = (uu___676_60455.all_implicits);
           goals = uu____60457;
           smt_goals = (uu___676_60455.smt_goals);
           depth = (uu___676_60455.depth);
           __dump = (uu___676_60455.__dump);
           psc = (uu___676_60455.psc);
           entry_range = (uu___676_60455.entry_range);
           guard_policy = (uu___676_60455.guard_policy);
           freshness = (uu___676_60455.freshness);
           tac_verb_dbg = (uu___676_60455.tac_verb_dbg);
           local_state = (uu___676_60455.local_state)
         })
  
let (decr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___679_60466 = ps  in
    {
      main_context = (uu___679_60466.main_context);
      main_goal = (uu___679_60466.main_goal);
      all_implicits = (uu___679_60466.all_implicits);
      goals = (uu___679_60466.goals);
      smt_goals = (uu___679_60466.smt_goals);
      depth = (ps.depth - (Prims.parse_int "1"));
      __dump = (uu___679_60466.__dump);
      psc = (uu___679_60466.psc);
      entry_range = (uu___679_60466.entry_range);
      guard_policy = (uu___679_60466.guard_policy);
      freshness = (uu___679_60466.freshness);
      tac_verb_dbg = (uu___679_60466.tac_verb_dbg);
      local_state = (uu___679_60466.local_state)
    }
  
let (incr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___682_60474 = ps  in
    {
      main_context = (uu___682_60474.main_context);
      main_goal = (uu___682_60474.main_goal);
      all_implicits = (uu___682_60474.all_implicits);
      goals = (uu___682_60474.goals);
      smt_goals = (uu___682_60474.smt_goals);
      depth = (ps.depth + (Prims.parse_int "1"));
      __dump = (uu___682_60474.__dump);
      psc = (uu___682_60474.psc);
      entry_range = (uu___682_60474.entry_range);
      guard_policy = (uu___682_60474.guard_policy);
      freshness = (uu___682_60474.freshness);
      tac_verb_dbg = (uu___682_60474.tac_verb_dbg);
      local_state = (uu___682_60474.local_state)
    }
  
let (tracepoint : proofstate -> unit) =
  fun ps  ->
    let uu____60482 =
      (FStar_Options.tactic_trace ()) ||
        (let uu____60485 = FStar_Options.tactic_trace_d ()  in
         ps.depth <= uu____60485)
       in
    if uu____60482
    then
      let uu____60488 =
        let uu____60489 = FStar_TypeChecker_Cfg.psc_subst ps.psc  in
        subst_proof_state uu____60489 ps  in
      ps.__dump uu____60488 "TRACE"
    else ()
  
let (set_ps_psc : FStar_TypeChecker_Cfg.psc -> proofstate -> proofstate) =
  fun psc  ->
    fun ps  ->
      let uu___688_60504 = ps  in
      {
        main_context = (uu___688_60504.main_context);
        main_goal = (uu___688_60504.main_goal);
        all_implicits = (uu___688_60504.all_implicits);
        goals = (uu___688_60504.goals);
        smt_goals = (uu___688_60504.smt_goals);
        depth = (uu___688_60504.depth);
        __dump = (uu___688_60504.__dump);
        psc;
        entry_range = (uu___688_60504.entry_range);
        guard_policy = (uu___688_60504.guard_policy);
        freshness = (uu___688_60504.freshness);
        tac_verb_dbg = (uu___688_60504.tac_verb_dbg);
        local_state = (uu___688_60504.local_state)
      }
  
let (set_proofstate_range : proofstate -> FStar_Range.range -> proofstate) =
  fun ps  ->
    fun r  ->
      let uu___692_60516 = ps  in
      let uu____60517 =
        let uu____60518 = FStar_Range.def_range r  in
        FStar_Range.set_def_range ps.entry_range uu____60518  in
      {
        main_context = (uu___692_60516.main_context);
        main_goal = (uu___692_60516.main_goal);
        all_implicits = (uu___692_60516.all_implicits);
        goals = (uu___692_60516.goals);
        smt_goals = (uu___692_60516.smt_goals);
        depth = (uu___692_60516.depth);
        __dump = (uu___692_60516.__dump);
        psc = (uu___692_60516.psc);
        entry_range = uu____60517;
        guard_policy = (uu___692_60516.guard_policy);
        freshness = (uu___692_60516.freshness);
        tac_verb_dbg = (uu___692_60516.tac_verb_dbg);
        local_state = (uu___692_60516.local_state)
      }
  
let (goals_of : proofstate -> goal Prims.list) = fun ps  -> ps.goals 
let (smt_goals_of : proofstate -> goal Prims.list) = fun ps  -> ps.smt_goals 
let (is_guard : goal -> Prims.bool) = fun g  -> g.is_guard 
let (get_label : goal -> Prims.string) = fun g  -> g.label 
let (set_label : Prims.string -> goal -> goal) =
  fun l  ->
    fun g  ->
      let uu___700_60566 = g  in
      {
        goal_main_env = (uu___700_60566.goal_main_env);
        goal_ctx_uvar = (uu___700_60566.goal_ctx_uvar);
        opts = (uu___700_60566.opts);
        is_guard = (uu___700_60566.is_guard);
        label = l
      }
  
type direction =
  | TopDown 
  | BottomUp 
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopDown  -> true | uu____60576 -> false
  
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | BottomUp  -> true | uu____60587 -> false
  
exception TacticFailure of Prims.string 
let (uu___is_TacticFailure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TacticFailure uu____60602 -> true
    | uu____60605 -> false
  
let (__proj__TacticFailure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | TacticFailure uu____60615 -> uu____60615
  
exception EExn of FStar_Syntax_Syntax.term 
let (uu___is_EExn : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | EExn uu____60629 -> true | uu____60631 -> false
  
let (__proj__EExn__item__uu___ : Prims.exn -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | EExn uu____60639 -> uu____60639 