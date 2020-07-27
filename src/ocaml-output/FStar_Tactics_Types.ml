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
let (goal_of_goal_ty :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> (goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun typ ->
      let uu____201 =
        FStar_TypeChecker_Env.new_implicit_var_aux "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
          FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None in
      match uu____201 with
      | (u, ctx_uvars, g_u) ->
          let uu____233 = FStar_List.hd ctx_uvars in
          (match uu____233 with
           | (ctx_uvar, uu____247) ->
               let g =
                 let uu____249 = FStar_Options.peek () in
                 mk_goal env ctx_uvar uu____249 false "" in
               (g, g_u))
let (goal_of_implicit :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.implicit -> goal) =
  fun env ->
    fun i ->
      let uu____260 = FStar_Options.peek () in
      mk_goal
        (let uu___52_263 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___52_263.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___52_263.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___52_263.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             ((i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___52_263.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___52_263.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___52_263.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___52_263.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___52_263.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___52_263.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___52_263.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___52_263.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___52_263.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___52_263.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___52_263.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___52_263.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___52_263.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___52_263.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___52_263.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___52_263.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___52_263.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___52_263.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___52_263.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___52_263.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___52_263.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___52_263.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___52_263.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___52_263.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___52_263.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___52_263.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___52_263.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___52_263.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___52_263.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___52_263.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___52_263.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___52_263.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___52_263.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___52_263.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___52_263.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___52_263.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___52_263.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___52_263.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___52_263.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___52_263.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___52_263.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___52_263.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___52_263.FStar_TypeChecker_Env.enable_defer_to_tac)
         }) i.FStar_TypeChecker_Common.imp_uvar uu____260 false
        i.FStar_TypeChecker_Common.imp_reason
let rename_binders :
  'uuuuuu270 .
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu270) Prims.list ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu270) Prims.list
  =
  fun subst ->
    fun bs ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu___0_330 ->
              match uu___0_330 with
              | (x, imp) ->
                  let y =
                    let uu____342 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst uu____342 in
                  let uu____343 =
                    let uu____344 = FStar_Syntax_Subst.compress y in
                    uu____344.FStar_Syntax_Syntax.n in
                  (match uu____343 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____352 =
                         let uu___63_353 = y1 in
                         let uu____354 =
                           FStar_Syntax_Subst.subst subst
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___63_353.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___63_353.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____354
                         } in
                       (uu____352, imp)
                   | uu____357 -> failwith "Not a renaming")))
let (subst_goal : FStar_Syntax_Syntax.subst_elt Prims.list -> goal -> goal) =
  fun subst ->
    fun goal1 ->
      let g = goal1.goal_ctx_uvar in
      let ctx_uvar =
        let uu___69_378 = g in
        let uu____379 =
          FStar_TypeChecker_Env.rename_gamma subst
            g.FStar_Syntax_Syntax.ctx_uvar_gamma in
        let uu____382 =
          rename_binders subst g.FStar_Syntax_Syntax.ctx_uvar_binders in
        let uu____393 =
          FStar_Syntax_Subst.subst subst g.FStar_Syntax_Syntax.ctx_uvar_typ in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___69_378.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma = uu____379;
          FStar_Syntax_Syntax.ctx_uvar_binders = uu____382;
          FStar_Syntax_Syntax.ctx_uvar_typ = uu____393;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___69_378.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___69_378.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___69_378.FStar_Syntax_Syntax.ctx_uvar_range);
          FStar_Syntax_Syntax.ctx_uvar_meta =
            (uu___69_378.FStar_Syntax_Syntax.ctx_uvar_meta)
        } in
      let uu___72_396 = goal1 in
      {
        goal_main_env = (uu___72_396.goal_main_env);
        goal_ctx_uvar = ctx_uvar;
        opts = (uu___72_396.opts);
        is_guard = (uu___72_396.is_guard);
        label = (uu___72_396.label)
      }
type guard_policy =
  | Goal 
  | SMT 
  | Force 
  | Drop 
let (uu___is_Goal : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | Goal -> true | uu____402 -> false
let (uu___is_SMT : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | SMT -> true | uu____408 -> false
let (uu___is_Force : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | Force -> true | uu____414 -> false
let (uu___is_Drop : guard_policy -> Prims.bool) =
  fun projectee -> match projectee with | Drop -> true | uu____420 -> false
type proofstate =
  {
  main_context: FStar_TypeChecker_Env.env ;
  all_implicits: FStar_TypeChecker_Common.implicits ;
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
  proofstate -> FStar_TypeChecker_Common.implicits) =
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
      let uu____881 = FStar_Options.tactic_raw_binders () in
      if uu____881
      then ps
      else
        (let uu___113_883 = ps in
         let uu____884 = FStar_List.map (subst_goal subst) ps.goals in
         {
           main_context = (uu___113_883.main_context);
           all_implicits = (uu___113_883.all_implicits);
           goals = uu____884;
           smt_goals = (uu___113_883.smt_goals);
           depth = (uu___113_883.depth);
           __dump = (uu___113_883.__dump);
           psc = (uu___113_883.psc);
           entry_range = (uu___113_883.entry_range);
           guard_policy = (uu___113_883.guard_policy);
           freshness = (uu___113_883.freshness);
           tac_verb_dbg = (uu___113_883.tac_verb_dbg);
           local_state = (uu___113_883.local_state)
         })
let (decr_depth : proofstate -> proofstate) =
  fun ps ->
    let uu___116_892 = ps in
    {
      main_context = (uu___116_892.main_context);
      all_implicits = (uu___116_892.all_implicits);
      goals = (uu___116_892.goals);
      smt_goals = (uu___116_892.smt_goals);
      depth = (ps.depth - Prims.int_one);
      __dump = (uu___116_892.__dump);
      psc = (uu___116_892.psc);
      entry_range = (uu___116_892.entry_range);
      guard_policy = (uu___116_892.guard_policy);
      freshness = (uu___116_892.freshness);
      tac_verb_dbg = (uu___116_892.tac_verb_dbg);
      local_state = (uu___116_892.local_state)
    }
let (incr_depth : proofstate -> proofstate) =
  fun ps ->
    let uu___119_898 = ps in
    {
      main_context = (uu___119_898.main_context);
      all_implicits = (uu___119_898.all_implicits);
      goals = (uu___119_898.goals);
      smt_goals = (uu___119_898.smt_goals);
      depth = (ps.depth + Prims.int_one);
      __dump = (uu___119_898.__dump);
      psc = (uu___119_898.psc);
      entry_range = (uu___119_898.entry_range);
      guard_policy = (uu___119_898.guard_policy);
      freshness = (uu___119_898.freshness);
      tac_verb_dbg = (uu___119_898.tac_verb_dbg);
      local_state = (uu___119_898.local_state)
    }
let (set_ps_psc : FStar_TypeChecker_Cfg.psc -> proofstate -> proofstate) =
  fun psc ->
    fun ps ->
      let uu___123_909 = ps in
      {
        main_context = (uu___123_909.main_context);
        all_implicits = (uu___123_909.all_implicits);
        goals = (uu___123_909.goals);
        smt_goals = (uu___123_909.smt_goals);
        depth = (uu___123_909.depth);
        __dump = (uu___123_909.__dump);
        psc;
        entry_range = (uu___123_909.entry_range);
        guard_policy = (uu___123_909.guard_policy);
        freshness = (uu___123_909.freshness);
        tac_verb_dbg = (uu___123_909.tac_verb_dbg);
        local_state = (uu___123_909.local_state)
      }
let (tracepoint : FStar_TypeChecker_Cfg.psc -> proofstate -> unit) =
  fun psc ->
    fun ps ->
      let uu____920 =
        (FStar_Options.tactic_trace ()) ||
          (let uu____922 = FStar_Options.tactic_trace_d () in
           ps.depth <= uu____922) in
      if uu____920
      then
        let ps1 = set_ps_psc psc ps in
        let subst = FStar_TypeChecker_Cfg.psc_subst ps1.psc in
        let uu____925 = subst_proof_state subst ps1 in
        ps1.__dump uu____925 "TRACE"
      else ()
let (set_proofstate_range : proofstate -> FStar_Range.range -> proofstate) =
  fun ps ->
    fun r ->
      let uu___132_937 = ps in
      let uu____938 =
        let uu____939 = FStar_Range.def_range r in
        FStar_Range.set_def_range ps.entry_range uu____939 in
      {
        main_context = (uu___132_937.main_context);
        all_implicits = (uu___132_937.all_implicits);
        goals = (uu___132_937.goals);
        smt_goals = (uu___132_937.smt_goals);
        depth = (uu___132_937.depth);
        __dump = (uu___132_937.__dump);
        psc = (uu___132_937.psc);
        entry_range = uu____938;
        guard_policy = (uu___132_937.guard_policy);
        freshness = (uu___132_937.freshness);
        tac_verb_dbg = (uu___132_937.tac_verb_dbg);
        local_state = (uu___132_937.local_state)
      }
let (goals_of : proofstate -> goal Prims.list) = fun ps -> ps.goals
let (smt_goals_of : proofstate -> goal Prims.list) = fun ps -> ps.smt_goals
let (is_guard : goal -> Prims.bool) = fun g -> g.is_guard
let (get_label : goal -> Prims.string) = fun g -> g.label
let (set_label : Prims.string -> goal -> goal) =
  fun l ->
    fun g ->
      let uu___140_978 = g in
      {
        goal_main_env = (uu___140_978.goal_main_env);
        goal_ctx_uvar = (uu___140_978.goal_ctx_uvar);
        opts = (uu___140_978.opts);
        is_guard = (uu___140_978.is_guard);
        label = l
      }
type direction =
  | TopDown 
  | BottomUp 
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee ->
    match projectee with | TopDown -> true | uu____984 -> false
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee ->
    match projectee with | BottomUp -> true | uu____990 -> false
type ctrl_flag =
  | Continue 
  | Skip 
  | Abort 
let (uu___is_Continue : ctrl_flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Continue -> true | uu____996 -> false
let (uu___is_Skip : ctrl_flag -> Prims.bool) =
  fun projectee -> match projectee with | Skip -> true | uu____1002 -> false
let (uu___is_Abort : ctrl_flag -> Prims.bool) =
  fun projectee -> match projectee with | Abort -> true | uu____1008 -> false
exception TacticFailure of Prims.string 
let (uu___is_TacticFailure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | TacticFailure uu____1018 -> true
    | uu____1019 -> false
let (__proj__TacticFailure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | TacticFailure uu____1025 -> uu____1025
exception EExn of FStar_Syntax_Syntax.term 
let (uu___is_EExn : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | EExn uu____1035 -> true | uu____1036 -> false
let (__proj__EExn__item__uu___ : Prims.exn -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | EExn uu____1042 -> uu____1042
let (check_goal_solved' :
  goal -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun goal1 ->
    let uu____1050 =
      FStar_Syntax_Unionfind.find
        (goal1.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
    match uu____1050 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (check_goal_solved : goal -> Prims.bool) =
  fun goal1 ->
    let uu____1061 = check_goal_solved' goal1 in
    FStar_Option.isSome uu____1061
let (get_phi :
  goal -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun g ->
    let uu____1073 =
      let uu____1074 = goal_env g in
      let uu____1075 = goal_type g in
      FStar_TypeChecker_Normalize.unfold_whnf uu____1074 uu____1075 in
    FStar_Syntax_Util.un_squash uu____1073
let (is_irrelevant : goal -> Prims.bool) =
  fun g -> let uu____1081 = get_phi g in FStar_Option.isSome uu____1081