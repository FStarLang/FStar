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
let (goal_env : goal -> FStar_TypeChecker_Env.env) =
  fun g ->
    let uu___16_119 = g.goal_main_env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___16_119.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___16_119.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___16_119.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma =
        ((g.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___16_119.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___16_119.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___16_119.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___16_119.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___16_119.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___16_119.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___16_119.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp =
        (uu___16_119.FStar_TypeChecker_Env.instantiate_imp);
      FStar_TypeChecker_Env.effects =
        (uu___16_119.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___16_119.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___16_119.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___16_119.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___16_119.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___16_119.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___16_119.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___16_119.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___16_119.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___16_119.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___16_119.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___16_119.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___16_119.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___16_119.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___16_119.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___16_119.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___16_119.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___16_119.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___16_119.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___16_119.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___16_119.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___16_119.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___16_119.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___16_119.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___16_119.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.postprocess =
        (uu___16_119.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___16_119.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___16_119.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___16_119.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___16_119.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___16_119.FStar_TypeChecker_Env.nbe)
    }
let (goal_witness : goal -> FStar_Syntax_Syntax.term) =
  fun g ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uvar
         ((g.goal_ctx_uvar), ([], FStar_Syntax_Syntax.NoUseRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
let (goal_type : goal -> FStar_Syntax_Syntax.term) =
  fun g -> (g.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
let (goal_with_type : goal -> FStar_Syntax_Syntax.term -> goal) =
  fun g ->
    fun t ->
      let c = g.goal_ctx_uvar in
      let c' =
        let uu___23_159 = c in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___23_159.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (uu___23_159.FStar_Syntax_Syntax.ctx_uvar_gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___23_159.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = t;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___23_159.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___23_159.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___23_159.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___23_159.FStar_Syntax_Syntax.ctx_uvar_meta)
        } in
      let uu___26_160 = g in
      {
        goal_main_env = (uu___26_160.goal_main_env);
        goal_ctx_uvar = c';
        opts = (uu___26_160.opts);
        is_guard = (uu___26_160.is_guard);
        label = (uu___26_160.label)
      }
let (goal_with_env : goal -> FStar_TypeChecker_Env.env -> goal) =
  fun g ->
    fun env ->
      let c = g.goal_ctx_uvar in
      let c' =
        let uu___31_174 = c in
        let uu____175 = FStar_TypeChecker_Env.all_binders env in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___31_174.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (env.FStar_TypeChecker_Env.gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders = uu____175;
          FStar_Syntax_Syntax.ctx_uvar_typ =
            (uu___31_174.FStar_Syntax_Syntax.ctx_uvar_typ);
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___31_174.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___31_174.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___31_174.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___31_174.FStar_Syntax_Syntax.ctx_uvar_meta)
        } in
      let uu___34_184 = g in
      {
        goal_main_env = env;
        goal_ctx_uvar = c';
        opts = (uu___34_184.opts);
        is_guard = (uu___34_184.is_guard);
        label = (uu___34_184.label)
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
let (subst_goal : FStar_Syntax_Syntax.subst_elt Prims.list -> goal -> goal) =
  fun subst1 ->
    fun goal ->
      let g = goal.goal_ctx_uvar in
      let ctx_uvar =
        let uu___44_232 = g in
        let uu____233 =
          FStar_TypeChecker_Env.rename_gamma subst1
            g.FStar_Syntax_Syntax.ctx_uvar_gamma in
        let uu____236 =
          FStar_Syntax_Subst.subst subst1 g.FStar_Syntax_Syntax.ctx_uvar_typ in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___44_232.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma = uu____233;
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___44_232.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = uu____236;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___44_232.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___44_232.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___44_232.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___44_232.FStar_Syntax_Syntax.ctx_uvar_meta)
        } in
      let uu___47_239 = goal in
      {
        goal_main_env = (uu___47_239.goal_main_env);
        goal_ctx_uvar = ctx_uvar;
        opts = (uu___47_239.opts);
        is_guard = (uu___47_239.is_guard);
        label = (uu___47_239.label)
      }
type guard_policy =
  | Goal 
  | SMT 
  | Force 
  | Drop 
let (uu___is_Goal : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | Goal -> true | uu____249 -> false
let (uu___is_SMT : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | SMT -> true | uu____260 -> false
let (uu___is_Force : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | Force -> true | uu____271 -> false
let (uu___is_Drop : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | Drop -> true | uu____282 -> false
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
  fun projectee ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> main_context
let (__proj__Mkproofstate__item__main_goal : proofstate -> goal) =
  fun projectee ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> main_goal
let (__proj__Mkproofstate__item__all_implicits :
  proofstate -> FStar_TypeChecker_Env.implicits) =
  fun projectee ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> all_implicits
let (__proj__Mkproofstate__item__goals : proofstate -> goal Prims.list) =
  fun projectee ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> goals
let (__proj__Mkproofstate__item__smt_goals : proofstate -> goal Prims.list) =
  fun projectee ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> smt_goals
let (__proj__Mkproofstate__item__depth : proofstate -> Prims.int) =
  fun projectee ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> depth
let (__proj__Mkproofstate__item____dump :
  proofstate -> proofstate -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> __dump
let (__proj__Mkproofstate__item__psc :
  proofstate -> FStar_TypeChecker_Cfg.psc) =
  fun projectee ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> psc
let (__proj__Mkproofstate__item__entry_range :
  proofstate -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> entry_range
let (__proj__Mkproofstate__item__guard_policy : proofstate -> guard_policy) =
  fun projectee ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> guard_policy
let (__proj__Mkproofstate__item__freshness : proofstate -> Prims.int) =
  fun projectee ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> freshness
let (__proj__Mkproofstate__item__tac_verb_dbg : proofstate -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> tac_verb_dbg
let (__proj__Mkproofstate__item__local_state :
  proofstate -> FStar_Syntax_Syntax.term FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { main_context; main_goal; all_implicits; goals; smt_goals; depth;
        __dump; psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> local_state
let (subst_proof_state :
  FStar_Syntax_Syntax.subst_t -> proofstate -> proofstate) =
  fun subst1 ->
    fun ps ->
      let uu____869 = FStar_Options.tactic_raw_binders () in
      if uu____869
      then ps
      else
        (let uu___91_874 = ps in
         let uu____875 = subst_goal subst1 ps.main_goal in
         let uu____876 = FStar_List.map (subst_goal subst1) ps.goals in
         {
           main_context = (uu___91_874.main_context);
           main_goal = uu____875;
           all_implicits = (uu___91_874.all_implicits);
           goals = uu____876;
           smt_goals = (uu___91_874.smt_goals);
           depth = (uu___91_874.depth);
           __dump = (uu___91_874.__dump);
           psc = (uu___91_874.psc);
           entry_range = (uu___91_874.entry_range);
           guard_policy = (uu___91_874.guard_policy);
           freshness = (uu___91_874.freshness);
           tac_verb_dbg = (uu___91_874.tac_verb_dbg);
           local_state = (uu___91_874.local_state)
         })
let (decr_depth : proofstate -> proofstate) =
  fun ps ->
    let uu___94_885 = ps in
    {
      main_context = (uu___94_885.main_context);
      main_goal = (uu___94_885.main_goal);
      all_implicits = (uu___94_885.all_implicits);
      goals = (uu___94_885.goals);
      smt_goals = (uu___94_885.smt_goals);
      depth = (ps.depth - (Prims.parse_int "1"));
      __dump = (uu___94_885.__dump);
      psc = (uu___94_885.psc);
      entry_range = (uu___94_885.entry_range);
      guard_policy = (uu___94_885.guard_policy);
      freshness = (uu___94_885.freshness);
      tac_verb_dbg = (uu___94_885.tac_verb_dbg);
      local_state = (uu___94_885.local_state)
    }
let (incr_depth : proofstate -> proofstate) =
  fun ps ->
    let uu___97_893 = ps in
    {
      main_context = (uu___97_893.main_context);
      main_goal = (uu___97_893.main_goal);
      all_implicits = (uu___97_893.all_implicits);
      goals = (uu___97_893.goals);
      smt_goals = (uu___97_893.smt_goals);
      depth = (ps.depth + (Prims.parse_int "1"));
      __dump = (uu___97_893.__dump);
      psc = (uu___97_893.psc);
      entry_range = (uu___97_893.entry_range);
      guard_policy = (uu___97_893.guard_policy);
      freshness = (uu___97_893.freshness);
      tac_verb_dbg = (uu___97_893.tac_verb_dbg);
      local_state = (uu___97_893.local_state)
    }
let (tracepoint : proofstate -> unit) =
  fun ps ->
    let uu____901 =
      (FStar_Options.tactic_trace ()) ||
        (let uu____904 = FStar_Options.tactic_trace_d () in
         ps.depth <= uu____904) in
    if uu____901
    then
      let uu____907 =
        let uu____908 = FStar_TypeChecker_Cfg.psc_subst ps.psc in
        subst_proof_state uu____908 ps in
      ps.__dump uu____907 "TRACE"
    else ()
let (set_ps_psc : FStar_TypeChecker_Cfg.psc -> proofstate -> proofstate) =
  fun psc ->
    fun ps ->
      let uu___103_923 = ps in
      {
        main_context = (uu___103_923.main_context);
        main_goal = (uu___103_923.main_goal);
        all_implicits = (uu___103_923.all_implicits);
        goals = (uu___103_923.goals);
        smt_goals = (uu___103_923.smt_goals);
        depth = (uu___103_923.depth);
        __dump = (uu___103_923.__dump);
        psc;
        entry_range = (uu___103_923.entry_range);
        guard_policy = (uu___103_923.guard_policy);
        freshness = (uu___103_923.freshness);
        tac_verb_dbg = (uu___103_923.tac_verb_dbg);
        local_state = (uu___103_923.local_state)
      }
let (set_proofstate_range : proofstate -> FStar_Range.range -> proofstate) =
  fun ps ->
    fun r ->
      let uu___107_935 = ps in
      let uu____936 =
        let uu____937 = FStar_Range.def_range r in
        FStar_Range.set_def_range ps.entry_range uu____937 in
      {
        main_context = (uu___107_935.main_context);
        main_goal = (uu___107_935.main_goal);
        all_implicits = (uu___107_935.all_implicits);
        goals = (uu___107_935.goals);
        smt_goals = (uu___107_935.smt_goals);
        depth = (uu___107_935.depth);
        __dump = (uu___107_935.__dump);
        psc = (uu___107_935.psc);
        entry_range = uu____936;
        guard_policy = (uu___107_935.guard_policy);
        freshness = (uu___107_935.freshness);
        tac_verb_dbg = (uu___107_935.tac_verb_dbg);
        local_state = (uu___107_935.local_state)
      }
let (goals_of : proofstate -> goal Prims.list) = fun ps -> ps.goals
let (smt_goals_of : proofstate -> goal Prims.list) = fun ps -> ps.smt_goals
let (is_guard : goal -> Prims.bool) = fun g -> g.is_guard
let (get_label : goal -> Prims.string) = fun g -> g.label
let (set_label : Prims.string -> goal -> goal) =
  fun l ->
    fun g ->
      let uu___115_985 = g in
      {
        goal_main_env = (uu___115_985.goal_main_env);
        goal_ctx_uvar = (uu___115_985.goal_ctx_uvar);
        opts = (uu___115_985.opts);
        is_guard = (uu___115_985.is_guard);
        label = l
      }
type direction =
  | TopDown 
  | BottomUp 
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee ->
    match projectee with | TopDown -> true | uu____995 -> false
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee ->
    match projectee with | BottomUp -> true | uu____1006 -> false
exception TacticFailure of Prims.string 
let (uu___is_TacticFailure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | TacticFailure uu____1021 -> true
    | uu____1024 -> false
let (__proj__TacticFailure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | TacticFailure uu____1034 -> uu____1034
exception EExn of FStar_Syntax_Syntax.term 
let (uu___is_EExn : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | EExn uu____1048 -> true | uu____1050 -> false
let (__proj__EExn__item__uu___ : Prims.exn -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | EExn uu____1058 -> uu____1058