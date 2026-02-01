open Prims
type goal =
  {
  goal_main_env: FStarC_TypeChecker_Env.env ;
  goal_ctx_uvar: FStarC_Syntax_Syntax.ctx_uvar ;
  opts: FStarC_Options.optionstate ;
  is_guard: Prims.bool ;
  label: Prims.string }
let __proj__Mkgoal__item__goal_main_env (projectee : goal) :
  FStarC_TypeChecker_Env.env=
  match projectee with
  | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} -> goal_main_env
let __proj__Mkgoal__item__goal_ctx_uvar (projectee : goal) :
  FStarC_Syntax_Syntax.ctx_uvar=
  match projectee with
  | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} -> goal_ctx_uvar
let __proj__Mkgoal__item__opts (projectee : goal) :
  FStarC_Options.optionstate=
  match projectee with
  | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} -> opts
let __proj__Mkgoal__item__is_guard (projectee : goal) : Prims.bool=
  match projectee with
  | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} -> is_guard
let __proj__Mkgoal__item__label (projectee : goal) : Prims.string=
  match projectee with
  | { goal_main_env; goal_ctx_uvar; opts; is_guard; label;_} -> label
type guard_policy =
  | Goal 
  | SMT 
  | SMTSync 
  | Force 
  | ForceSMT 
  | Drop 
let uu___is_Goal (projectee : guard_policy) : Prims.bool=
  match projectee with | Goal -> true | uu___ -> false
let uu___is_SMT (projectee : guard_policy) : Prims.bool=
  match projectee with | SMT -> true | uu___ -> false
let uu___is_SMTSync (projectee : guard_policy) : Prims.bool=
  match projectee with | SMTSync -> true | uu___ -> false
let uu___is_Force (projectee : guard_policy) : Prims.bool=
  match projectee with | Force -> true | uu___ -> false
let uu___is_ForceSMT (projectee : guard_policy) : Prims.bool=
  match projectee with | ForceSMT -> true | uu___ -> false
let uu___is_Drop (projectee : guard_policy) : Prims.bool=
  match projectee with | Drop -> true | uu___ -> false
let showable_guard_policy : guard_policy FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Goal -> "Goal"
         | SMT -> "SMT"
         | SMTSync -> "SMTSync"
         | Force -> "Force"
         | ForceSMT -> "ForceSMT"
         | Drop -> "Drop")
  }
let pretty_guard_policy : guard_policy FStarC_Class_PP.pretty=
  FStarC_Class_PP.pretty_from_showable showable_guard_policy
type proofstate =
  {
  main_context: FStarC_TypeChecker_Env.env ;
  all_implicits: FStarC_TypeChecker_Common.implicits ;
  goals: goal Prims.list ;
  smt_goals: goal Prims.list ;
  splice_quals: FStarC_Syntax_Syntax.qualifier Prims.list ;
  splice_attrs: FStarC_Syntax_Syntax.attribute Prims.list ;
  depth: Prims.int ;
  __dump: proofstate -> Prims.string -> unit ;
  psc: FStarC_TypeChecker_Primops_Base.psc ;
  entry_range: FStarC_Range_Type.t ;
  guard_policy: guard_policy ;
  freshness: Prims.int ;
  tac_verb_dbg: Prims.bool ;
  local_state: FStarC_Syntax_Syntax.term FStarC_PSMap.t ;
  urgency: Prims.int ;
  dump_on_failure: Prims.bool }
let __proj__Mkproofstate__item__main_context (projectee : proofstate) :
  FStarC_TypeChecker_Env.env=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> main_context
let __proj__Mkproofstate__item__all_implicits (projectee : proofstate) :
  FStarC_TypeChecker_Common.implicits=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> all_implicits
let __proj__Mkproofstate__item__goals (projectee : proofstate) :
  goal Prims.list=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> goals
let __proj__Mkproofstate__item__smt_goals (projectee : proofstate) :
  goal Prims.list=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> smt_goals
let __proj__Mkproofstate__item__splice_quals (projectee : proofstate) :
  FStarC_Syntax_Syntax.qualifier Prims.list=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> splice_quals
let __proj__Mkproofstate__item__splice_attrs (projectee : proofstate) :
  FStarC_Syntax_Syntax.attribute Prims.list=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> splice_attrs
let __proj__Mkproofstate__item__depth (projectee : proofstate) : Prims.int=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> depth
let __proj__Mkproofstate__item____dump (projectee : proofstate) :
  proofstate -> Prims.string -> unit=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> __dump
let __proj__Mkproofstate__item__psc (projectee : proofstate) :
  FStarC_TypeChecker_Primops_Base.psc=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> psc
let __proj__Mkproofstate__item__entry_range (projectee : proofstate) :
  FStarC_Range_Type.t=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> entry_range
let __proj__Mkproofstate__item__guard_policy (projectee : proofstate) :
  guard_policy=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> guard_policy1
let __proj__Mkproofstate__item__freshness (projectee : proofstate) :
  Prims.int=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> freshness
let __proj__Mkproofstate__item__tac_verb_dbg (projectee : proofstate) :
  Prims.bool=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> tac_verb_dbg
let __proj__Mkproofstate__item__local_state (projectee : proofstate) :
  FStarC_Syntax_Syntax.term FStarC_PSMap.t=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> local_state
let __proj__Mkproofstate__item__urgency (projectee : proofstate) : Prims.int=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> urgency
let __proj__Mkproofstate__item__dump_on_failure (projectee : proofstate) :
  Prims.bool=
  match projectee with
  | { main_context; all_implicits; goals; smt_goals; splice_quals;
      splice_attrs; depth; __dump; psc; entry_range;
      guard_policy = guard_policy1; freshness; tac_verb_dbg; local_state;
      urgency; dump_on_failure;_} -> dump_on_failure
type ref_proofstate = proofstate FStarC_Effect.ref
let goal_env (g : goal) : FStarC_TypeChecker_Env.env= g.goal_main_env
let goal_range (g : goal) : FStarC_Range_Type.t=
  (g.goal_main_env).FStarC_TypeChecker_Env.range
let goal_witness (g : goal) : FStarC_Syntax_Syntax.term=
  FStarC_Syntax_Syntax.mk
    (FStarC_Syntax_Syntax.Tm_uvar
       ((g.goal_ctx_uvar), ([], FStarC_Syntax_Syntax.NoUseRange)))
    FStarC_Range_Type.dummyRange
let goal_type (g : goal) : FStarC_Syntax_Syntax.term=
  FStarC_Syntax_Util.ctx_uvar_typ g.goal_ctx_uvar
let goal_opts (g : goal) : FStarC_Options.optionstate= g.opts
let goal_with_env (g : goal) (env : FStarC_TypeChecker_Env.env) : goal=
  let c = g.goal_ctx_uvar in
  let c' =
    let uu___ = FStarC_TypeChecker_Env.all_binders env in
    {
      FStarC_Syntax_Syntax.ctx_uvar_head =
        (c.FStarC_Syntax_Syntax.ctx_uvar_head);
      FStarC_Syntax_Syntax.ctx_uvar_gamma =
        (env.FStarC_TypeChecker_Env.gamma);
      FStarC_Syntax_Syntax.ctx_uvar_binders = uu___;
      FStarC_Syntax_Syntax.ctx_uvar_reason =
        (c.FStarC_Syntax_Syntax.ctx_uvar_reason);
      FStarC_Syntax_Syntax.ctx_uvar_range =
        (c.FStarC_Syntax_Syntax.ctx_uvar_range);
      FStarC_Syntax_Syntax.ctx_uvar_meta =
        (c.FStarC_Syntax_Syntax.ctx_uvar_meta)
    } in
  {
    goal_main_env = env;
    goal_ctx_uvar = c';
    opts = (g.opts);
    is_guard = (g.is_guard);
    label = (g.label)
  }
let goal_of_ctx_uvar (g : goal) (ctx_u : FStarC_Syntax_Syntax.ctx_uvar) :
  goal=
  {
    goal_main_env = (g.goal_main_env);
    goal_ctx_uvar = ctx_u;
    opts = (g.opts);
    is_guard = (g.is_guard);
    label = (g.label)
  }
let mk_goal (env : FStarC_TypeChecker_Env.env)
  (u : FStarC_Syntax_Syntax.ctx_uvar) (o : FStarC_Options.optionstate)
  (b : Prims.bool) (l : Prims.string) : goal=
  { goal_main_env = env; goal_ctx_uvar = u; opts = o; is_guard = b; label = l
  }
let goal_of_goal_ty (env : FStarC_TypeChecker_Env.env)
  (typ : FStarC_Syntax_Syntax.typ) :
  (goal * FStarC_TypeChecker_Common.guard_t)=
  let uu___ =
    FStarC_TypeChecker_Env.new_implicit_var_aux "proofstate_of_goal_ty"
      typ.FStarC_Syntax_Syntax.pos env typ FStarC_Syntax_Syntax.Strict
      FStar_Pervasives_Native.None false in
  match uu___ with
  | (u, (ctx_uvar, uu___1), g_u) ->
      let g =
        let uu___2 = FStarC_Options.peek () in
        mk_goal env ctx_uvar uu___2 false "" in
      (g, g_u)
let goal_of_implicit (env : FStarC_TypeChecker_Env.env)
  (i : FStarC_TypeChecker_Env.implicit) : goal=
  let uu___ = FStarC_Options.peek () in
  mk_goal
    {
      FStarC_TypeChecker_Env.solver = (env.FStarC_TypeChecker_Env.solver);
      FStarC_TypeChecker_Env.range = (env.FStarC_TypeChecker_Env.range);
      FStarC_TypeChecker_Env.curmodule =
        (env.FStarC_TypeChecker_Env.curmodule);
      FStarC_TypeChecker_Env.gamma =
        ((i.FStarC_TypeChecker_Common.imp_uvar).FStarC_Syntax_Syntax.ctx_uvar_gamma);
      FStarC_TypeChecker_Env.gamma_sig =
        (env.FStarC_TypeChecker_Env.gamma_sig);
      FStarC_TypeChecker_Env.gamma_cache =
        (env.FStarC_TypeChecker_Env.gamma_cache);
      FStarC_TypeChecker_Env.modules = (env.FStarC_TypeChecker_Env.modules);
      FStarC_TypeChecker_Env.expected_typ =
        (env.FStarC_TypeChecker_Env.expected_typ);
      FStarC_TypeChecker_Env.sigtab = (env.FStarC_TypeChecker_Env.sigtab);
      FStarC_TypeChecker_Env.attrtab = (env.FStarC_TypeChecker_Env.attrtab);
      FStarC_TypeChecker_Env.instantiate_imp =
        (env.FStarC_TypeChecker_Env.instantiate_imp);
      FStarC_TypeChecker_Env.effects = (env.FStarC_TypeChecker_Env.effects);
      FStarC_TypeChecker_Env.generalize =
        (env.FStarC_TypeChecker_Env.generalize);
      FStarC_TypeChecker_Env.letrecs = (env.FStarC_TypeChecker_Env.letrecs);
      FStarC_TypeChecker_Env.top_level =
        (env.FStarC_TypeChecker_Env.top_level);
      FStarC_TypeChecker_Env.check_uvars =
        (env.FStarC_TypeChecker_Env.check_uvars);
      FStarC_TypeChecker_Env.use_eq_strict =
        (env.FStarC_TypeChecker_Env.use_eq_strict);
      FStarC_TypeChecker_Env.is_iface = (env.FStarC_TypeChecker_Env.is_iface);
      FStarC_TypeChecker_Env.admit = (env.FStarC_TypeChecker_Env.admit);
      FStarC_TypeChecker_Env.phase1 = (env.FStarC_TypeChecker_Env.phase1);
      FStarC_TypeChecker_Env.failhard = (env.FStarC_TypeChecker_Env.failhard);
      FStarC_TypeChecker_Env.flychecking =
        (env.FStarC_TypeChecker_Env.flychecking);
      FStarC_TypeChecker_Env.uvar_subtyping =
        (env.FStarC_TypeChecker_Env.uvar_subtyping);
      FStarC_TypeChecker_Env.intactics =
        (env.FStarC_TypeChecker_Env.intactics);
      FStarC_TypeChecker_Env.nocoerce = (env.FStarC_TypeChecker_Env.nocoerce);
      FStarC_TypeChecker_Env.tc_term = (env.FStarC_TypeChecker_Env.tc_term);
      FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
        (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
      FStarC_TypeChecker_Env.universe_of =
        (env.FStarC_TypeChecker_Env.universe_of);
      FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
        (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
      FStarC_TypeChecker_Env.teq_nosmt_force =
        (env.FStarC_TypeChecker_Env.teq_nosmt_force);
      FStarC_TypeChecker_Env.subtype_nosmt_force =
        (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
      FStarC_TypeChecker_Env.qtbl_name_and_index =
        (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
      FStarC_TypeChecker_Env.normalized_eff_names =
        (env.FStarC_TypeChecker_Env.normalized_eff_names);
      FStarC_TypeChecker_Env.fv_delta_depths =
        (env.FStarC_TypeChecker_Env.fv_delta_depths);
      FStarC_TypeChecker_Env.proof_ns = (env.FStarC_TypeChecker_Env.proof_ns);
      FStarC_TypeChecker_Env.synth_hook =
        (env.FStarC_TypeChecker_Env.synth_hook);
      FStarC_TypeChecker_Env.try_solve_implicits_hook =
        (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
      FStarC_TypeChecker_Env.splice = (env.FStarC_TypeChecker_Env.splice);
      FStarC_TypeChecker_Env.mpreprocess =
        (env.FStarC_TypeChecker_Env.mpreprocess);
      FStarC_TypeChecker_Env.postprocess =
        (env.FStarC_TypeChecker_Env.postprocess);
      FStarC_TypeChecker_Env.identifier_info =
        (env.FStarC_TypeChecker_Env.identifier_info);
      FStarC_TypeChecker_Env.tc_hooks = (env.FStarC_TypeChecker_Env.tc_hooks);
      FStarC_TypeChecker_Env.dsenv = (env.FStarC_TypeChecker_Env.dsenv);
      FStarC_TypeChecker_Env.nbe = (env.FStarC_TypeChecker_Env.nbe);
      FStarC_TypeChecker_Env.strict_args_tab =
        (env.FStarC_TypeChecker_Env.strict_args_tab);
      FStarC_TypeChecker_Env.erasable_types_tab =
        (env.FStarC_TypeChecker_Env.erasable_types_tab);
      FStarC_TypeChecker_Env.enable_defer_to_tac =
        (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
      FStarC_TypeChecker_Env.unif_allow_ref_guards =
        (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
      FStarC_TypeChecker_Env.erase_erasable_args =
        (env.FStarC_TypeChecker_Env.erase_erasable_args);
      FStarC_TypeChecker_Env.core_check =
        (env.FStarC_TypeChecker_Env.core_check);
      FStarC_TypeChecker_Env.missing_decl =
        (env.FStarC_TypeChecker_Env.missing_decl)
    } i.FStarC_TypeChecker_Common.imp_uvar uu___ false
    i.FStarC_TypeChecker_Common.imp_reason
let decr_depth (ps : proofstate) : proofstate=
  {
    main_context = (ps.main_context);
    all_implicits = (ps.all_implicits);
    goals = (ps.goals);
    smt_goals = (ps.smt_goals);
    splice_quals = (ps.splice_quals);
    splice_attrs = (ps.splice_attrs);
    depth = (ps.depth - Prims.int_one);
    __dump = (ps.__dump);
    psc = (ps.psc);
    entry_range = (ps.entry_range);
    guard_policy = (ps.guard_policy);
    freshness = (ps.freshness);
    tac_verb_dbg = (ps.tac_verb_dbg);
    local_state = (ps.local_state);
    urgency = (ps.urgency);
    dump_on_failure = (ps.dump_on_failure)
  }
let incr_depth (ps : proofstate) : proofstate=
  {
    main_context = (ps.main_context);
    all_implicits = (ps.all_implicits);
    goals = (ps.goals);
    smt_goals = (ps.smt_goals);
    splice_quals = (ps.splice_quals);
    splice_attrs = (ps.splice_attrs);
    depth = (ps.depth + Prims.int_one);
    __dump = (ps.__dump);
    psc = (ps.psc);
    entry_range = (ps.entry_range);
    guard_policy = (ps.guard_policy);
    freshness = (ps.freshness);
    tac_verb_dbg = (ps.tac_verb_dbg);
    local_state = (ps.local_state);
    urgency = (ps.urgency);
    dump_on_failure = (ps.dump_on_failure)
  }
let set_ps_psc (psc : FStarC_TypeChecker_Primops_Base.psc) (ps : proofstate)
  : proofstate=
  {
    main_context = (ps.main_context);
    all_implicits = (ps.all_implicits);
    goals = (ps.goals);
    smt_goals = (ps.smt_goals);
    splice_quals = (ps.splice_quals);
    splice_attrs = (ps.splice_attrs);
    depth = (ps.depth);
    __dump = (ps.__dump);
    psc;
    entry_range = (ps.entry_range);
    guard_policy = (ps.guard_policy);
    freshness = (ps.freshness);
    tac_verb_dbg = (ps.tac_verb_dbg);
    local_state = (ps.local_state);
    urgency = (ps.urgency);
    dump_on_failure = (ps.dump_on_failure)
  }
let tracepoint_with_psc (psc : FStarC_TypeChecker_Primops_Base.psc)
  (ps : proofstate) : Prims.bool=
  (let uu___1 =
     (FStarC_Options.tactic_trace ()) ||
       (let uu___2 = FStarC_Options.tactic_trace_d () in ps.depth <= uu___2) in
   if uu___1
   then let ps1 = set_ps_psc psc ps in ps1.__dump ps1 "TRACE"
   else ());
  true
let tracepoint (ps : proofstate) : Prims.bool=
  (let uu___1 =
     (FStarC_Options.tactic_trace ()) ||
       (let uu___2 = FStarC_Options.tactic_trace_d () in ps.depth <= uu___2) in
   if uu___1 then ps.__dump ps "TRACE" else ());
  true
let set_proofstate_range (ps : proofstate) (r : FStarC_Range_Type.t) :
  proofstate=
  let uu___ =
    let uu___1 = FStarC_Range_Type.def_range r in
    FStarC_Range_Type.set_def_range ps.entry_range uu___1 in
  {
    main_context = (ps.main_context);
    all_implicits = (ps.all_implicits);
    goals = (ps.goals);
    smt_goals = (ps.smt_goals);
    splice_quals = (ps.splice_quals);
    splice_attrs = (ps.splice_attrs);
    depth = (ps.depth);
    __dump = (ps.__dump);
    psc = (ps.psc);
    entry_range = uu___;
    guard_policy = (ps.guard_policy);
    freshness = (ps.freshness);
    tac_verb_dbg = (ps.tac_verb_dbg);
    local_state = (ps.local_state);
    urgency = (ps.urgency);
    dump_on_failure = (ps.dump_on_failure)
  }
let goals_of (ps : proofstate) : goal Prims.list= ps.goals
let smt_goals_of (ps : proofstate) : goal Prims.list= ps.smt_goals
let is_guard (g : goal) : Prims.bool= g.is_guard
let get_label (g : goal) : Prims.string= g.label
let set_label (l : Prims.string) (g : goal) : goal=
  {
    goal_main_env = (g.goal_main_env);
    goal_ctx_uvar = (g.goal_ctx_uvar);
    opts = (g.opts);
    is_guard = (g.is_guard);
    label = l
  }
type ctrl_flag =
  | Continue 
  | Skip 
  | Abort 
let uu___is_Continue (projectee : ctrl_flag) : Prims.bool=
  match projectee with | Continue -> true | uu___ -> false
let uu___is_Skip (projectee : ctrl_flag) : Prims.bool=
  match projectee with | Skip -> true | uu___ -> false
let uu___is_Abort (projectee : ctrl_flag) : Prims.bool=
  match projectee with | Abort -> true | uu___ -> false
type direction =
  | TopDown 
  | BottomUp 
let uu___is_TopDown (projectee : direction) : Prims.bool=
  match projectee with | TopDown -> true | uu___ -> false
let uu___is_BottomUp (projectee : direction) : Prims.bool=
  match projectee with | BottomUp -> true | uu___ -> false
let check_goal_solved' (goal1 : goal) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_Syntax_Unionfind.find
      (goal1.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_head in
  match uu___ with
  | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let check_goal_solved (goal1 : goal) : Prims.bool=
  let uu___ = check_goal_solved' goal1 in
  FStar_Pervasives_Native.uu___is_Some uu___
type 'a tref = 'a FStarC_Effect.ref
