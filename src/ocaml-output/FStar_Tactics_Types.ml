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
        let uu___22_133 = c in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___22_133.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (uu___22_133.FStar_Syntax_Syntax.ctx_uvar_gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___22_133.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = t;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___22_133.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___22_133.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___22_133.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___22_133.FStar_Syntax_Syntax.ctx_uvar_meta)
        } in
      let uu___25_134 = g in
      {
        goal_main_env = (uu___25_134.goal_main_env);
        goal_ctx_uvar = c';
        opts = (uu___25_134.opts);
        is_guard = (uu___25_134.is_guard);
        label = (uu___25_134.label)
      }
let (goal_with_env : goal -> FStar_TypeChecker_Env.env -> goal) =
  fun g ->
    fun env ->
      let c = g.goal_ctx_uvar in
      let c' =
        let uu___30_147 = c in
        let uu____148 = FStar_TypeChecker_Env.all_binders env in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___30_147.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (env.FStar_TypeChecker_Env.gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders = uu____148;
          FStar_Syntax_Syntax.ctx_uvar_typ =
            (uu___30_147.FStar_Syntax_Syntax.ctx_uvar_typ);
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___30_147.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___30_147.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___30_147.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___30_147.FStar_Syntax_Syntax.ctx_uvar_meta)
        } in
      let uu___33_157 = g in
      {
        goal_main_env = env;
        goal_ctx_uvar = c';
        opts = (uu___33_157.opts);
        is_guard = (uu___33_157.is_guard);
        label = (uu___33_157.label)
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
let rename_binders :
  'uuuuuu189 .
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu189) Prims.list ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu189) Prims.list
  =
  fun subst ->
    fun bs ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu___0_249 ->
              match uu___0_249 with
              | (x, imp) ->
                  let y =
                    let uu____261 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst uu____261 in
                  let uu____262 =
                    let uu____263 = FStar_Syntax_Subst.compress y in
                    uu____263.FStar_Syntax_Syntax.n in
                  (match uu____262 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____271 =
                         let uu___49_272 = y1 in
                         let uu____273 =
                           FStar_Syntax_Subst.subst subst
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___49_272.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___49_272.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____273
                         } in
                       (uu____271, imp)
                   | uu____276 -> failwith "Not a renaming")))
let (subst_goal : FStar_Syntax_Syntax.subst_elt Prims.list -> goal -> goal) =
  fun subst ->
    fun goal1 ->
      let g = goal1.goal_ctx_uvar in
      let ctx_uvar =
        let uu___55_297 = g in
        let uu____298 =
          FStar_TypeChecker_Env.rename_gamma subst
            g.FStar_Syntax_Syntax.ctx_uvar_gamma in
        let uu____301 =
          rename_binders subst g.FStar_Syntax_Syntax.ctx_uvar_binders in
        let uu____312 =
          FStar_Syntax_Subst.subst subst g.FStar_Syntax_Syntax.ctx_uvar_typ in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___55_297.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma = uu____298;
          FStar_Syntax_Syntax.ctx_uvar_binders = uu____301;
          FStar_Syntax_Syntax.ctx_uvar_typ = uu____312;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___55_297.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___55_297.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___55_297.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___55_297.FStar_Syntax_Syntax.ctx_uvar_meta)
        } in
      let uu___58_315 = goal1 in
      {
        goal_main_env = (uu___58_315.goal_main_env);
        goal_ctx_uvar = ctx_uvar;
        opts = (uu___58_315.opts);
        is_guard = (uu___58_315.is_guard);
        label = (uu___58_315.label)
      }
type guard_policy =
  | Goal 
  | SMT 
  | Force 
  | Drop 
let (uu___is_Goal : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | Goal -> true | uu____321 -> false
let (uu___is_SMT : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | SMT -> true | uu____327 -> false
let (uu___is_Force : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | Force -> true | uu____333 -> false
let (uu___is_Drop : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | Drop -> true | uu____339 -> false
type proofstate =
  {
  main_context: FStar_TypeChecker_Env.env ;
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
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state;_} -> main_context
let (__proj__Mkproofstate__item__all_implicits :
  proofstate -> FStar_TypeChecker_Env.implicits) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state;_} -> all_implicits
let (__proj__Mkproofstate__item__goals : proofstate -> goal Prims.list) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state;_} -> goals
let (__proj__Mkproofstate__item__smt_goals : proofstate -> goal Prims.list) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state;_} -> smt_goals
let (__proj__Mkproofstate__item__depth : proofstate -> Prims.int) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state;_} -> depth
let (__proj__Mkproofstate__item____dump :
  proofstate -> proofstate -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state;_} -> __dump
let (__proj__Mkproofstate__item__psc :
  proofstate -> FStar_TypeChecker_Cfg.psc) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state;_} -> psc
let (__proj__Mkproofstate__item__entry_range :
  proofstate -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state;_} -> entry_range
let (__proj__Mkproofstate__item__guard_policy : proofstate -> guard_policy) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state;_} -> guard_policy1
let (__proj__Mkproofstate__item__freshness : proofstate -> Prims.int) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state;_} -> freshness
let (__proj__Mkproofstate__item__tac_verb_dbg : proofstate -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state;_} -> tac_verb_dbg
let (__proj__Mkproofstate__item__local_state :
  proofstate -> FStar_Syntax_Syntax.term FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy = guard_policy1; freshness;
        tac_verb_dbg; local_state;_} -> local_state
let (subst_proof_state :
  FStar_Syntax_Syntax.subst_t -> proofstate -> proofstate) =
  fun subst ->
    fun ps ->
      let uu____800 = FStar_Options.tactic_raw_binders () in
      if uu____800
      then ps
      else
        (let uu___99_802 = ps in
         let uu____803 = FStar_List.map (subst_goal subst) ps.goals in
         {
           main_context = (uu___99_802.main_context);
           all_implicits = (uu___99_802.all_implicits);
           goals = uu____803;
           smt_goals = (uu___99_802.smt_goals);
           depth = (uu___99_802.depth);
           __dump = (uu___99_802.__dump);
           psc = (uu___99_802.psc);
           entry_range = (uu___99_802.entry_range);
           guard_policy = (uu___99_802.guard_policy);
           freshness = (uu___99_802.freshness);
           tac_verb_dbg = (uu___99_802.tac_verb_dbg);
           local_state = (uu___99_802.local_state)
         })
let (decr_depth : proofstate -> proofstate) =
  fun ps ->
    let uu___102_811 = ps in
    {
      main_context = (uu___102_811.main_context);
      all_implicits = (uu___102_811.all_implicits);
      goals = (uu___102_811.goals);
      smt_goals = (uu___102_811.smt_goals);
      depth = (ps.depth - Prims.int_one);
      __dump = (uu___102_811.__dump);
      psc = (uu___102_811.psc);
      entry_range = (uu___102_811.entry_range);
      guard_policy = (uu___102_811.guard_policy);
      freshness = (uu___102_811.freshness);
      tac_verb_dbg = (uu___102_811.tac_verb_dbg);
      local_state = (uu___102_811.local_state)
    }
let (incr_depth : proofstate -> proofstate) =
  fun ps ->
    let uu___105_817 = ps in
    {
      main_context = (uu___105_817.main_context);
      all_implicits = (uu___105_817.all_implicits);
      goals = (uu___105_817.goals);
      smt_goals = (uu___105_817.smt_goals);
      depth = (ps.depth + Prims.int_one);
      __dump = (uu___105_817.__dump);
      psc = (uu___105_817.psc);
      entry_range = (uu___105_817.entry_range);
      guard_policy = (uu___105_817.guard_policy);
      freshness = (uu___105_817.freshness);
      tac_verb_dbg = (uu___105_817.tac_verb_dbg);
      local_state = (uu___105_817.local_state)
    }
let (set_ps_psc : FStar_TypeChecker_Cfg.psc -> proofstate -> proofstate) =
  fun psc ->
    fun ps ->
      let uu___109_828 = ps in
      {
        main_context = (uu___109_828.main_context);
        all_implicits = (uu___109_828.all_implicits);
        goals = (uu___109_828.goals);
        smt_goals = (uu___109_828.smt_goals);
        depth = (uu___109_828.depth);
        __dump = (uu___109_828.__dump);
        psc;
        entry_range = (uu___109_828.entry_range);
        guard_policy = (uu___109_828.guard_policy);
        freshness = (uu___109_828.freshness);
        tac_verb_dbg = (uu___109_828.tac_verb_dbg);
        local_state = (uu___109_828.local_state)
      }
let (tracepoint : FStar_TypeChecker_Cfg.psc -> proofstate -> unit) =
  fun psc ->
    fun ps ->
      let uu____839 =
        (FStar_Options.tactic_trace ()) ||
          (let uu____841 = FStar_Options.tactic_trace_d () in
           ps.depth <= uu____841) in
      if uu____839
      then
        let ps1 = set_ps_psc psc ps in
        let subst = FStar_TypeChecker_Cfg.psc_subst ps1.psc in
        let uu____844 = subst_proof_state subst ps1 in
        ps1.__dump uu____844 "TRACE"
      else ()
let (set_proofstate_range : proofstate -> FStar_Range.range -> proofstate) =
  fun ps ->
    fun r ->
      let uu___118_856 = ps in
      let uu____857 =
        let uu____858 = FStar_Range.def_range r in
        FStar_Range.set_def_range ps.entry_range uu____858 in
      {
        main_context = (uu___118_856.main_context);
        all_implicits = (uu___118_856.all_implicits);
        goals = (uu___118_856.goals);
        smt_goals = (uu___118_856.smt_goals);
        depth = (uu___118_856.depth);
        __dump = (uu___118_856.__dump);
        psc = (uu___118_856.psc);
        entry_range = uu____857;
        guard_policy = (uu___118_856.guard_policy);
        freshness = (uu___118_856.freshness);
        tac_verb_dbg = (uu___118_856.tac_verb_dbg);
        local_state = (uu___118_856.local_state)
      }
let (goals_of : proofstate -> goal Prims.list) = fun ps -> ps.goals
let (smt_goals_of : proofstate -> goal Prims.list) = fun ps -> ps.smt_goals
let (is_guard : goal -> Prims.bool) = fun g -> g.is_guard
let (get_label : goal -> Prims.string) = fun g -> g.label
let (set_label : Prims.string -> goal -> goal) =
  fun l ->
    fun g ->
      let uu___126_897 = g in
      {
        goal_main_env = (uu___126_897.goal_main_env);
        goal_ctx_uvar = (uu___126_897.goal_ctx_uvar);
        opts = (uu___126_897.opts);
        is_guard = (uu___126_897.is_guard);
        label = l
      }
type direction =
  | TopDown 
  | BottomUp 
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee ->
    match projectee with | TopDown -> true | uu____903 -> false
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee ->
    match projectee with | BottomUp -> true | uu____909 -> false
type ctrl_flag =
  | Continue 
  | Skip 
  | Abort 
let (uu___is_Continue : ctrl_flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Continue -> true | uu____915 -> false
let (uu___is_Skip : ctrl_flag -> Prims.bool) =
  fun projectee -> match projectee with | Skip -> true | uu____921 -> false
let (uu___is_Abort : ctrl_flag -> Prims.bool) =
  fun projectee -> match projectee with | Abort -> true | uu____927 -> false
let (check_goal_solved' :
  goal -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun goal1 ->
    let uu____935 =
      FStar_Syntax_Unionfind.find
        (goal1.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
    match uu____935 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (check_goal_solved : goal -> Prims.bool) =
  fun goal1 ->
    let uu____946 = check_goal_solved' goal1 in FStar_Option.isSome uu____946
let (get_phi :
  goal -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun g ->
    let uu____958 =
      let uu____959 = goal_env g in
      let uu____960 = goal_type g in
      FStar_TypeChecker_Normalize.unfold_whnf uu____959 uu____960 in
    FStar_Syntax_Util.un_squash uu____958
let (is_irrelevant : goal -> Prims.bool) =
  fun g -> let uu____966 = get_phi g in FStar_Option.isSome uu____966