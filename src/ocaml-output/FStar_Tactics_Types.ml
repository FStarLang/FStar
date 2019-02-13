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
    let uu___260_102 = g.goal_main_env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___260_102.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range =
        (uu___260_102.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___260_102.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma =
        ((g.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___260_102.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___260_102.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___260_102.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___260_102.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___260_102.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___260_102.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___260_102.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp =
        (uu___260_102.FStar_TypeChecker_Env.instantiate_imp);
      FStar_TypeChecker_Env.effects =
        (uu___260_102.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___260_102.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___260_102.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___260_102.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___260_102.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___260_102.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___260_102.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit =
        (uu___260_102.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___260_102.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___260_102.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___260_102.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___260_102.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___260_102.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___260_102.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___260_102.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___260_102.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___260_102.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___260_102.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___260_102.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___260_102.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___260_102.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___260_102.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___260_102.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___260_102.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___260_102.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.postprocess =
        (uu___260_102.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___260_102.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___260_102.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___260_102.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv =
        (uu___260_102.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___260_102.FStar_TypeChecker_Env.nbe)
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
        let uu___261_142 = c  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___261_142.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (uu___261_142.FStar_Syntax_Syntax.ctx_uvar_gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___261_142.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = t;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___261_142.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___261_142.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___261_142.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___261_142.FStar_Syntax_Syntax.ctx_uvar_meta)
        }  in
      let uu___262_143 = g  in
      {
        goal_main_env = (uu___262_143.goal_main_env);
        goal_ctx_uvar = c';
        opts = (uu___262_143.opts);
        is_guard = (uu___262_143.is_guard);
        label = (uu___262_143.label)
      }
  
let (goal_with_env : goal -> FStar_TypeChecker_Env.env -> goal) =
  fun g  ->
    fun env  ->
      let c = g.goal_ctx_uvar  in
      let c' =
        let uu___263_157 = c  in
        let uu____158 = FStar_TypeChecker_Env.all_binders env  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___263_157.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (env.FStar_TypeChecker_Env.gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders = uu____158;
          FStar_Syntax_Syntax.ctx_uvar_typ =
            (uu___263_157.FStar_Syntax_Syntax.ctx_uvar_typ);
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___263_157.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___263_157.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___263_157.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___263_157.FStar_Syntax_Syntax.ctx_uvar_meta)
        }  in
      let uu___264_167 = g  in
      {
        goal_main_env = env;
        goal_ctx_uvar = c';
        opts = (uu___264_167.opts);
        is_guard = (uu___264_167.is_guard);
        label = (uu___264_167.label)
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
        let uu___265_215 = g  in
        let uu____216 =
          FStar_TypeChecker_Env.rename_gamma subst1
            g.FStar_Syntax_Syntax.ctx_uvar_gamma
           in
        let uu____219 =
          FStar_Syntax_Subst.subst subst1 g.FStar_Syntax_Syntax.ctx_uvar_typ
           in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___265_215.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma = uu____216;
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___265_215.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = uu____219;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___265_215.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___265_215.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___265_215.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___265_215.FStar_Syntax_Syntax.ctx_uvar_meta)
        }  in
      let uu___266_222 = goal  in
      {
        goal_main_env = (uu___266_222.goal_main_env);
        goal_ctx_uvar = ctx_uvar;
        opts = (uu___266_222.opts);
        is_guard = (uu___266_222.is_guard);
        label = (uu___266_222.label)
      }
  
type guard_policy =
  | Goal 
  | SMT 
  | Force 
  | Drop 
let (uu___is_Goal : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Goal  -> true | uu____232 -> false 
let (uu___is_SMT : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | SMT  -> true | uu____243 -> false 
let (uu___is_Force : guard_policy -> Prims.bool) =
  fun projectee  ->
    match projectee with | Force  -> true | uu____254 -> false
  
let (uu___is_Drop : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Drop  -> true | uu____265 -> false 
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
      let uu____852 = FStar_Options.tactic_raw_binders ()  in
      if uu____852
      then ps
      else
        (let uu___267_857 = ps  in
         let uu____858 = subst_goal subst1 ps.main_goal  in
         let uu____859 = FStar_List.map (subst_goal subst1) ps.goals  in
         {
           main_context = (uu___267_857.main_context);
           main_goal = uu____858;
           all_implicits = (uu___267_857.all_implicits);
           goals = uu____859;
           smt_goals = (uu___267_857.smt_goals);
           depth = (uu___267_857.depth);
           __dump = (uu___267_857.__dump);
           psc = (uu___267_857.psc);
           entry_range = (uu___267_857.entry_range);
           guard_policy = (uu___267_857.guard_policy);
           freshness = (uu___267_857.freshness);
           tac_verb_dbg = (uu___267_857.tac_verb_dbg);
           local_state = (uu___267_857.local_state)
         })
  
let (decr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___268_868 = ps  in
    {
      main_context = (uu___268_868.main_context);
      main_goal = (uu___268_868.main_goal);
      all_implicits = (uu___268_868.all_implicits);
      goals = (uu___268_868.goals);
      smt_goals = (uu___268_868.smt_goals);
      depth = (ps.depth - (Prims.parse_int "1"));
      __dump = (uu___268_868.__dump);
      psc = (uu___268_868.psc);
      entry_range = (uu___268_868.entry_range);
      guard_policy = (uu___268_868.guard_policy);
      freshness = (uu___268_868.freshness);
      tac_verb_dbg = (uu___268_868.tac_verb_dbg);
      local_state = (uu___268_868.local_state)
    }
  
let (incr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___269_876 = ps  in
    {
      main_context = (uu___269_876.main_context);
      main_goal = (uu___269_876.main_goal);
      all_implicits = (uu___269_876.all_implicits);
      goals = (uu___269_876.goals);
      smt_goals = (uu___269_876.smt_goals);
      depth = (ps.depth + (Prims.parse_int "1"));
      __dump = (uu___269_876.__dump);
      psc = (uu___269_876.psc);
      entry_range = (uu___269_876.entry_range);
      guard_policy = (uu___269_876.guard_policy);
      freshness = (uu___269_876.freshness);
      tac_verb_dbg = (uu___269_876.tac_verb_dbg);
      local_state = (uu___269_876.local_state)
    }
  
let (tracepoint : proofstate -> unit) =
  fun ps  ->
    let uu____884 =
      (FStar_Options.tactic_trace ()) ||
        (let uu____887 = FStar_Options.tactic_trace_d ()  in
         ps.depth <= uu____887)
       in
    if uu____884
    then
      let uu____890 =
        let uu____891 = FStar_TypeChecker_Cfg.psc_subst ps.psc  in
        subst_proof_state uu____891 ps  in
      ps.__dump uu____890 "TRACE"
    else ()
  
let (set_ps_psc : FStar_TypeChecker_Cfg.psc -> proofstate -> proofstate) =
  fun psc  ->
    fun ps  ->
      let uu___270_906 = ps  in
      {
        main_context = (uu___270_906.main_context);
        main_goal = (uu___270_906.main_goal);
        all_implicits = (uu___270_906.all_implicits);
        goals = (uu___270_906.goals);
        smt_goals = (uu___270_906.smt_goals);
        depth = (uu___270_906.depth);
        __dump = (uu___270_906.__dump);
        psc;
        entry_range = (uu___270_906.entry_range);
        guard_policy = (uu___270_906.guard_policy);
        freshness = (uu___270_906.freshness);
        tac_verb_dbg = (uu___270_906.tac_verb_dbg);
        local_state = (uu___270_906.local_state)
      }
  
let (set_proofstate_range : proofstate -> FStar_Range.range -> proofstate) =
  fun ps  ->
    fun r  ->
      let uu___271_918 = ps  in
      let uu____919 =
        let uu____920 = FStar_Range.def_range r  in
        FStar_Range.set_def_range ps.entry_range uu____920  in
      {
        main_context = (uu___271_918.main_context);
        main_goal = (uu___271_918.main_goal);
        all_implicits = (uu___271_918.all_implicits);
        goals = (uu___271_918.goals);
        smt_goals = (uu___271_918.smt_goals);
        depth = (uu___271_918.depth);
        __dump = (uu___271_918.__dump);
        psc = (uu___271_918.psc);
        entry_range = uu____919;
        guard_policy = (uu___271_918.guard_policy);
        freshness = (uu___271_918.freshness);
        tac_verb_dbg = (uu___271_918.tac_verb_dbg);
        local_state = (uu___271_918.local_state)
      }
  
let (goals_of : proofstate -> goal Prims.list) = fun ps  -> ps.goals 
let (smt_goals_of : proofstate -> goal Prims.list) = fun ps  -> ps.smt_goals 
let (is_guard : goal -> Prims.bool) = fun g  -> g.is_guard 
let (get_label : goal -> Prims.string) = fun g  -> g.label 
let (set_label : Prims.string -> goal -> goal) =
  fun l  ->
    fun g  ->
      let uu___272_968 = g  in
      {
        goal_main_env = (uu___272_968.goal_main_env);
        goal_ctx_uvar = (uu___272_968.goal_ctx_uvar);
        opts = (uu___272_968.opts);
        is_guard = (uu___272_968.is_guard);
        label = l
      }
  
type direction =
  | TopDown 
  | BottomUp 
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopDown  -> true | uu____978 -> false
  
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | BottomUp  -> true | uu____989 -> false
  
exception TacticFailure of Prims.string 
let (uu___is_TacticFailure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TacticFailure uu____1004 -> true
    | uu____1007 -> false
  
let (__proj__TacticFailure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | TacticFailure uu____1018 -> uu____1018
  
exception EExn of FStar_Syntax_Syntax.term 
let (uu___is_EExn : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | EExn uu____1032 -> true | uu____1034 -> false
  
let (__proj__EExn__item__uu___ : Prims.exn -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | EExn uu____1043 -> uu____1043 