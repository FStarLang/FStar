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
    let uu___17_119 = g.goal_main_env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___17_119.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___17_119.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___17_119.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma =
        ((g.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___17_119.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___17_119.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___17_119.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___17_119.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___17_119.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___17_119.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___17_119.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp =
        (uu___17_119.FStar_TypeChecker_Env.instantiate_imp);
      FStar_TypeChecker_Env.effects =
        (uu___17_119.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___17_119.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___17_119.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___17_119.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___17_119.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___17_119.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___17_119.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___17_119.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___17_119.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___17_119.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___17_119.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___17_119.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___17_119.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___17_119.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___17_119.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___17_119.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___17_119.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___17_119.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___17_119.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___17_119.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___17_119.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___17_119.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___17_119.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___17_119.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___17_119.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.postprocess =
        (uu___17_119.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___17_119.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___17_119.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___17_119.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___17_119.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___17_119.FStar_TypeChecker_Env.nbe);
      FStar_TypeChecker_Env.strict_args_tab =
        (uu___17_119.FStar_TypeChecker_Env.strict_args_tab);
      FStar_TypeChecker_Env.erasable_types_tab =
        (uu___17_119.FStar_TypeChecker_Env.erasable_types_tab)
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
        let uu___24_159 = c  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___24_159.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (uu___24_159.FStar_Syntax_Syntax.ctx_uvar_gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___24_159.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = t;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___24_159.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___24_159.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___24_159.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___24_159.FStar_Syntax_Syntax.ctx_uvar_meta)
        }  in
      let uu___27_160 = g  in
      {
        goal_main_env = (uu___27_160.goal_main_env);
        goal_ctx_uvar = c';
        opts = (uu___27_160.opts);
        is_guard = (uu___27_160.is_guard);
        label = (uu___27_160.label)
      }
  
let (goal_with_env : goal -> FStar_TypeChecker_Env.env -> goal) =
  fun g  ->
    fun env  ->
      let c = g.goal_ctx_uvar  in
      let c' =
        let uu___32_174 = c  in
        let uu____175 = FStar_TypeChecker_Env.all_binders env  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___32_174.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (env.FStar_TypeChecker_Env.gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders = uu____175;
          FStar_Syntax_Syntax.ctx_uvar_typ =
            (uu___32_174.FStar_Syntax_Syntax.ctx_uvar_typ);
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___32_174.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___32_174.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___32_174.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___32_174.FStar_Syntax_Syntax.ctx_uvar_meta)
        }  in
      let uu___35_184 = g  in
      {
        goal_main_env = env;
        goal_ctx_uvar = c';
        opts = (uu___35_184.opts);
        is_guard = (uu___35_184.is_guard);
        label = (uu___35_184.label)
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
  
let rename_binders :
  'Auu____222 .
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____222) Prims.list ->
        (FStar_Syntax_Syntax.bv * 'Auu____222) Prims.list
  =
  fun subst1  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu___0_282  ->
              match uu___0_282 with
              | (x,imp) ->
                  let y =
                    let uu____294 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____294  in
                  let uu____295 =
                    let uu____296 = FStar_Syntax_Subst.compress y  in
                    uu____296.FStar_Syntax_Syntax.n  in
                  (match uu____295 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____304 =
                         let uu___51_305 = y1  in
                         let uu____306 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___51_305.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___51_305.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____306
                         }  in
                       (uu____304, imp)
                   | uu____309 -> failwith "Not a renaming")))
  
let (subst_goal : FStar_Syntax_Syntax.subst_elt Prims.list -> goal -> goal) =
  fun subst1  ->
    fun goal  ->
      let g = goal.goal_ctx_uvar  in
      let ctx_uvar =
        let uu___57_332 = g  in
        let uu____333 =
          FStar_TypeChecker_Env.rename_gamma subst1
            g.FStar_Syntax_Syntax.ctx_uvar_gamma
           in
        let uu____336 =
          rename_binders subst1 g.FStar_Syntax_Syntax.ctx_uvar_binders  in
        let uu____347 =
          FStar_Syntax_Subst.subst subst1 g.FStar_Syntax_Syntax.ctx_uvar_typ
           in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___57_332.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma = uu____333;
          FStar_Syntax_Syntax.ctx_uvar_binders = uu____336;
          FStar_Syntax_Syntax.ctx_uvar_typ = uu____347;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___57_332.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___57_332.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___57_332.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___57_332.FStar_Syntax_Syntax.ctx_uvar_meta)
        }  in
      let uu___60_350 = goal  in
      {
        goal_main_env = (uu___60_350.goal_main_env);
        goal_ctx_uvar = ctx_uvar;
        opts = (uu___60_350.opts);
        is_guard = (uu___60_350.is_guard);
        label = (uu___60_350.label)
      }
  
type guard_policy =
  | Goal 
  | SMT 
  | Force 
  | Drop 
let (uu___is_Goal : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Goal  -> true | uu____360 -> false 
let (uu___is_SMT : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | SMT  -> true | uu____371 -> false 
let (uu___is_Force : guard_policy -> Prims.bool) =
  fun projectee  ->
    match projectee with | Force  -> true | uu____382 -> false
  
let (uu___is_Drop : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Drop  -> true | uu____393 -> false 
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
      let uu____980 = FStar_Options.tactic_raw_binders ()  in
      if uu____980
      then ps
      else
        (let uu___104_985 = ps  in
         let uu____986 = subst_goal subst1 ps.main_goal  in
         let uu____987 = FStar_List.map (subst_goal subst1) ps.goals  in
         {
           main_context = (uu___104_985.main_context);
           main_goal = uu____986;
           all_implicits = (uu___104_985.all_implicits);
           goals = uu____987;
           smt_goals = (uu___104_985.smt_goals);
           depth = (uu___104_985.depth);
           __dump = (uu___104_985.__dump);
           psc = (uu___104_985.psc);
           entry_range = (uu___104_985.entry_range);
           guard_policy = (uu___104_985.guard_policy);
           freshness = (uu___104_985.freshness);
           tac_verb_dbg = (uu___104_985.tac_verb_dbg);
           local_state = (uu___104_985.local_state)
         })
  
let (decr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___107_996 = ps  in
    {
      main_context = (uu___107_996.main_context);
      main_goal = (uu___107_996.main_goal);
      all_implicits = (uu___107_996.all_implicits);
      goals = (uu___107_996.goals);
      smt_goals = (uu___107_996.smt_goals);
      depth = (ps.depth - Prims.int_one);
      __dump = (uu___107_996.__dump);
      psc = (uu___107_996.psc);
      entry_range = (uu___107_996.entry_range);
      guard_policy = (uu___107_996.guard_policy);
      freshness = (uu___107_996.freshness);
      tac_verb_dbg = (uu___107_996.tac_verb_dbg);
      local_state = (uu___107_996.local_state)
    }
  
let (incr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___110_1004 = ps  in
    {
      main_context = (uu___110_1004.main_context);
      main_goal = (uu___110_1004.main_goal);
      all_implicits = (uu___110_1004.all_implicits);
      goals = (uu___110_1004.goals);
      smt_goals = (uu___110_1004.smt_goals);
      depth = (ps.depth + Prims.int_one);
      __dump = (uu___110_1004.__dump);
      psc = (uu___110_1004.psc);
      entry_range = (uu___110_1004.entry_range);
      guard_policy = (uu___110_1004.guard_policy);
      freshness = (uu___110_1004.freshness);
      tac_verb_dbg = (uu___110_1004.tac_verb_dbg);
      local_state = (uu___110_1004.local_state)
    }
  
let (set_ps_psc : FStar_TypeChecker_Cfg.psc -> proofstate -> proofstate) =
  fun psc  ->
    fun ps  ->
      let uu___114_1017 = ps  in
      {
        main_context = (uu___114_1017.main_context);
        main_goal = (uu___114_1017.main_goal);
        all_implicits = (uu___114_1017.all_implicits);
        goals = (uu___114_1017.goals);
        smt_goals = (uu___114_1017.smt_goals);
        depth = (uu___114_1017.depth);
        __dump = (uu___114_1017.__dump);
        psc;
        entry_range = (uu___114_1017.entry_range);
        guard_policy = (uu___114_1017.guard_policy);
        freshness = (uu___114_1017.freshness);
        tac_verb_dbg = (uu___114_1017.tac_verb_dbg);
        local_state = (uu___114_1017.local_state)
      }
  
let (tracepoint : FStar_TypeChecker_Cfg.psc -> proofstate -> unit) =
  fun psc  ->
    fun ps  ->
      let uu____1029 =
        (FStar_Options.tactic_trace ()) ||
          (let uu____1032 = FStar_Options.tactic_trace_d ()  in
           ps.depth <= uu____1032)
         in
      if uu____1029
      then
        let ps1 = set_ps_psc psc ps  in
        let subst1 = FStar_TypeChecker_Cfg.psc_subst ps1.psc  in
        let uu____1037 = subst_proof_state subst1 ps1  in
        ps1.__dump uu____1037 "TRACE"
      else ()
  
let (set_proofstate_range : proofstate -> FStar_Range.range -> proofstate) =
  fun ps  ->
    fun r  ->
      let uu___123_1052 = ps  in
      let uu____1053 =
        let uu____1054 = FStar_Range.def_range r  in
        FStar_Range.set_def_range ps.entry_range uu____1054  in
      {
        main_context = (uu___123_1052.main_context);
        main_goal = (uu___123_1052.main_goal);
        all_implicits = (uu___123_1052.all_implicits);
        goals = (uu___123_1052.goals);
        smt_goals = (uu___123_1052.smt_goals);
        depth = (uu___123_1052.depth);
        __dump = (uu___123_1052.__dump);
        psc = (uu___123_1052.psc);
        entry_range = uu____1053;
        guard_policy = (uu___123_1052.guard_policy);
        freshness = (uu___123_1052.freshness);
        tac_verb_dbg = (uu___123_1052.tac_verb_dbg);
        local_state = (uu___123_1052.local_state)
      }
  
let (goals_of : proofstate -> goal Prims.list) = fun ps  -> ps.goals 
let (smt_goals_of : proofstate -> goal Prims.list) = fun ps  -> ps.smt_goals 
let (is_guard : goal -> Prims.bool) = fun g  -> g.is_guard 
let (get_label : goal -> Prims.string) = fun g  -> g.label 
let (set_label : Prims.string -> goal -> goal) =
  fun l  ->
    fun g  ->
      let uu___131_1102 = g  in
      {
        goal_main_env = (uu___131_1102.goal_main_env);
        goal_ctx_uvar = (uu___131_1102.goal_ctx_uvar);
        opts = (uu___131_1102.opts);
        is_guard = (uu___131_1102.is_guard);
        label = l
      }
  
type direction =
  | TopDown 
  | BottomUp 
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopDown  -> true | uu____1112 -> false
  
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | BottomUp  -> true | uu____1123 -> false
  
exception TacticFailure of Prims.string 
let (uu___is_TacticFailure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TacticFailure uu____1138 -> true
    | uu____1141 -> false
  
let (__proj__TacticFailure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | TacticFailure uu____1151 -> uu____1151
  
exception EExn of FStar_Syntax_Syntax.term 
let (uu___is_EExn : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | EExn uu____1165 -> true | uu____1167 -> false
  
let (__proj__EExn__item__uu___ : Prims.exn -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | EExn uu____1175 -> uu____1175 