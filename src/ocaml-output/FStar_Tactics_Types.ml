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
  fun g  -> g.goal_main_env 
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
        let uu___22_157 = c  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___22_157.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (uu___22_157.FStar_Syntax_Syntax.ctx_uvar_gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___22_157.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = t;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___22_157.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___22_157.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___22_157.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___22_157.FStar_Syntax_Syntax.ctx_uvar_meta)
        }  in
      let uu___25_158 = g  in
      {
        goal_main_env = (uu___25_158.goal_main_env);
        goal_ctx_uvar = c';
        opts = (uu___25_158.opts);
        is_guard = (uu___25_158.is_guard);
        label = (uu___25_158.label)
      }
  
let (goal_with_env : goal -> FStar_TypeChecker_Env.env -> goal) =
  fun g  ->
    fun env  ->
      let c = g.goal_ctx_uvar  in
      let c' =
        let uu___30_172 = c  in
        let uu____173 = FStar_TypeChecker_Env.all_binders env  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___30_172.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (env.FStar_TypeChecker_Env.gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders = uu____173;
          FStar_Syntax_Syntax.ctx_uvar_typ =
            (uu___30_172.FStar_Syntax_Syntax.ctx_uvar_typ);
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___30_172.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___30_172.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___30_172.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___30_172.FStar_Syntax_Syntax.ctx_uvar_meta)
        }  in
      let uu___33_182 = g  in
      {
        goal_main_env = env;
        goal_ctx_uvar = c';
        opts = (uu___33_182.opts);
        is_guard = (uu___33_182.is_guard);
        label = (uu___33_182.label)
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
  'Auu____220 .
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____220) Prims.list ->
        (FStar_Syntax_Syntax.bv * 'Auu____220) Prims.list
  =
  fun subst1  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu___0_280  ->
              match uu___0_280 with
              | (x,imp) ->
                  let y =
                    let uu____292 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____292  in
                  let uu____293 =
                    let uu____294 = FStar_Syntax_Subst.compress y  in
                    uu____294.FStar_Syntax_Syntax.n  in
                  (match uu____293 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____302 =
                         let uu___49_303 = y1  in
                         let uu____304 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___49_303.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___49_303.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____304
                         }  in
                       (uu____302, imp)
                   | uu____307 -> failwith "Not a renaming")))
  
let (subst_goal : FStar_Syntax_Syntax.subst_elt Prims.list -> goal -> goal) =
  fun subst1  ->
    fun goal  ->
      let g = goal.goal_ctx_uvar  in
      let ctx_uvar =
        let uu___55_330 = g  in
        let uu____331 =
          FStar_TypeChecker_Env.rename_gamma subst1
            g.FStar_Syntax_Syntax.ctx_uvar_gamma
           in
        let uu____334 =
          rename_binders subst1 g.FStar_Syntax_Syntax.ctx_uvar_binders  in
        let uu____345 =
          FStar_Syntax_Subst.subst subst1 g.FStar_Syntax_Syntax.ctx_uvar_typ
           in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___55_330.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma = uu____331;
          FStar_Syntax_Syntax.ctx_uvar_binders = uu____334;
          FStar_Syntax_Syntax.ctx_uvar_typ = uu____345;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___55_330.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___55_330.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___55_330.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___55_330.FStar_Syntax_Syntax.ctx_uvar_meta)
        }  in
      let uu___58_348 = goal  in
      {
        goal_main_env = (uu___58_348.goal_main_env);
        goal_ctx_uvar = ctx_uvar;
        opts = (uu___58_348.opts);
        is_guard = (uu___58_348.is_guard);
        label = (uu___58_348.label)
      }
  
type guard_policy =
  | Goal 
  | SMT 
  | Force 
  | Drop 
let (uu___is_Goal : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Goal  -> true | uu____358 -> false 
let (uu___is_SMT : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | SMT  -> true | uu____369 -> false 
let (uu___is_Force : guard_policy -> Prims.bool) =
  fun projectee  ->
    match projectee with | Force  -> true | uu____380 -> false
  
let (uu___is_Drop : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Drop  -> true | uu____391 -> false 
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
  fun projectee  ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> main_context
  
let (__proj__Mkproofstate__item__all_implicits :
  proofstate -> FStar_TypeChecker_Env.implicits) =
  fun projectee  ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> all_implicits
  
let (__proj__Mkproofstate__item__goals : proofstate -> goal Prims.list) =
  fun projectee  ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> goals
  
let (__proj__Mkproofstate__item__smt_goals : proofstate -> goal Prims.list) =
  fun projectee  ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> smt_goals
  
let (__proj__Mkproofstate__item__depth : proofstate -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> depth
  
let (__proj__Mkproofstate__item____dump :
  proofstate -> proofstate -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> __dump
  
let (__proj__Mkproofstate__item__psc :
  proofstate -> FStar_TypeChecker_Cfg.psc) =
  fun projectee  ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> psc
  
let (__proj__Mkproofstate__item__entry_range :
  proofstate -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> entry_range
  
let (__proj__Mkproofstate__item__guard_policy : proofstate -> guard_policy) =
  fun projectee  ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> guard_policy
  
let (__proj__Mkproofstate__item__freshness : proofstate -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> freshness
  
let (__proj__Mkproofstate__item__tac_verb_dbg : proofstate -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> tac_verb_dbg
  
let (__proj__Mkproofstate__item__local_state :
  proofstate -> FStar_Syntax_Syntax.term FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { main_context; all_implicits; goals; smt_goals; depth; __dump; 
        psc; entry_range; guard_policy; freshness; tac_verb_dbg;
        local_state;_} -> local_state
  
let (subst_proof_state :
  FStar_Syntax_Syntax.subst_t -> proofstate -> proofstate) =
  fun subst1  ->
    fun ps  ->
      let uu____926 = FStar_Options.tactic_raw_binders ()  in
      if uu____926
      then ps
      else
        (let uu___99_931 = ps  in
         let uu____932 = FStar_List.map (subst_goal subst1) ps.goals  in
         {
           main_context = (uu___99_931.main_context);
           all_implicits = (uu___99_931.all_implicits);
           goals = uu____932;
           smt_goals = (uu___99_931.smt_goals);
           depth = (uu___99_931.depth);
           __dump = (uu___99_931.__dump);
           psc = (uu___99_931.psc);
           entry_range = (uu___99_931.entry_range);
           guard_policy = (uu___99_931.guard_policy);
           freshness = (uu___99_931.freshness);
           tac_verb_dbg = (uu___99_931.tac_verb_dbg);
           local_state = (uu___99_931.local_state)
         })
  
let (decr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___102_941 = ps  in
    {
      main_context = (uu___102_941.main_context);
      all_implicits = (uu___102_941.all_implicits);
      goals = (uu___102_941.goals);
      smt_goals = (uu___102_941.smt_goals);
      depth = (ps.depth - Prims.int_one);
      __dump = (uu___102_941.__dump);
      psc = (uu___102_941.psc);
      entry_range = (uu___102_941.entry_range);
      guard_policy = (uu___102_941.guard_policy);
      freshness = (uu___102_941.freshness);
      tac_verb_dbg = (uu___102_941.tac_verb_dbg);
      local_state = (uu___102_941.local_state)
    }
  
let (incr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___105_949 = ps  in
    {
      main_context = (uu___105_949.main_context);
      all_implicits = (uu___105_949.all_implicits);
      goals = (uu___105_949.goals);
      smt_goals = (uu___105_949.smt_goals);
      depth = (ps.depth + Prims.int_one);
      __dump = (uu___105_949.__dump);
      psc = (uu___105_949.psc);
      entry_range = (uu___105_949.entry_range);
      guard_policy = (uu___105_949.guard_policy);
      freshness = (uu___105_949.freshness);
      tac_verb_dbg = (uu___105_949.tac_verb_dbg);
      local_state = (uu___105_949.local_state)
    }
  
let (set_ps_psc : FStar_TypeChecker_Cfg.psc -> proofstate -> proofstate) =
  fun psc  ->
    fun ps  ->
      let uu___109_962 = ps  in
      {
        main_context = (uu___109_962.main_context);
        all_implicits = (uu___109_962.all_implicits);
        goals = (uu___109_962.goals);
        smt_goals = (uu___109_962.smt_goals);
        depth = (uu___109_962.depth);
        __dump = (uu___109_962.__dump);
        psc;
        entry_range = (uu___109_962.entry_range);
        guard_policy = (uu___109_962.guard_policy);
        freshness = (uu___109_962.freshness);
        tac_verb_dbg = (uu___109_962.tac_verb_dbg);
        local_state = (uu___109_962.local_state)
      }
  
let (tracepoint : FStar_TypeChecker_Cfg.psc -> proofstate -> unit) =
  fun psc  ->
    fun ps  ->
      let uu____974 =
        (FStar_Options.tactic_trace ()) ||
          (let uu____977 = FStar_Options.tactic_trace_d ()  in
           ps.depth <= uu____977)
         in
      if uu____974
      then
        let ps1 = set_ps_psc psc ps  in
        let subst1 = FStar_TypeChecker_Cfg.psc_subst ps1.psc  in
        let uu____982 = subst_proof_state subst1 ps1  in
        ps1.__dump uu____982 "TRACE"
      else ()
  
let (set_proofstate_range : proofstate -> FStar_Range.range -> proofstate) =
  fun ps  ->
    fun r  ->
      let uu___118_997 = ps  in
      let uu____998 =
        let uu____999 = FStar_Range.def_range r  in
        FStar_Range.set_def_range ps.entry_range uu____999  in
      {
        main_context = (uu___118_997.main_context);
        all_implicits = (uu___118_997.all_implicits);
        goals = (uu___118_997.goals);
        smt_goals = (uu___118_997.smt_goals);
        depth = (uu___118_997.depth);
        __dump = (uu___118_997.__dump);
        psc = (uu___118_997.psc);
        entry_range = uu____998;
        guard_policy = (uu___118_997.guard_policy);
        freshness = (uu___118_997.freshness);
        tac_verb_dbg = (uu___118_997.tac_verb_dbg);
        local_state = (uu___118_997.local_state)
      }
  
let (goals_of : proofstate -> goal Prims.list) = fun ps  -> ps.goals 
let (smt_goals_of : proofstate -> goal Prims.list) = fun ps  -> ps.smt_goals 
let (is_guard : goal -> Prims.bool) = fun g  -> g.is_guard 
let (get_label : goal -> Prims.string) = fun g  -> g.label 
let (set_label : Prims.string -> goal -> goal) =
  fun l  ->
    fun g  ->
      let uu___126_1047 = g  in
      {
        goal_main_env = (uu___126_1047.goal_main_env);
        goal_ctx_uvar = (uu___126_1047.goal_ctx_uvar);
        opts = (uu___126_1047.opts);
        is_guard = (uu___126_1047.is_guard);
        label = l
      }
  
type direction =
  | TopDown 
  | BottomUp 
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopDown  -> true | uu____1057 -> false
  
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | BottomUp  -> true | uu____1068 -> false
  
exception TacticFailure of Prims.string 
let (uu___is_TacticFailure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TacticFailure uu____1083 -> true
    | uu____1086 -> false
  
let (__proj__TacticFailure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | TacticFailure uu____1096 -> uu____1096
  
exception EExn of FStar_Syntax_Syntax.term 
let (uu___is_EExn : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | EExn uu____1110 -> true | uu____1112 -> false
  
let (__proj__EExn__item__uu___ : Prims.exn -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | EExn uu____1120 -> uu____1120 