
open Prims
open FStar_Pervasives
type goal =
{goal_main_env : FStar_TypeChecker_Env.env; goal_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar; opts : FStar_Options.optionstate; is_guard : Prims.bool; label : Prims.string}


let __proj__Mkgoal__item__goal_main_env : goal  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {goal_main_env = goal_main_env; goal_ctx_uvar = goal_ctx_uvar; opts = opts; is_guard = is_guard; label = label} -> begin
goal_main_env
end))


let __proj__Mkgoal__item__goal_ctx_uvar : goal  ->  FStar_Syntax_Syntax.ctx_uvar = (fun projectee -> (match (projectee) with
| {goal_main_env = goal_main_env; goal_ctx_uvar = goal_ctx_uvar; opts = opts; is_guard = is_guard; label = label} -> begin
goal_ctx_uvar
end))


let __proj__Mkgoal__item__opts : goal  ->  FStar_Options.optionstate = (fun projectee -> (match (projectee) with
| {goal_main_env = goal_main_env; goal_ctx_uvar = goal_ctx_uvar; opts = opts; is_guard = is_guard; label = label} -> begin
opts
end))


let __proj__Mkgoal__item__is_guard : goal  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {goal_main_env = goal_main_env; goal_ctx_uvar = goal_ctx_uvar; opts = opts; is_guard = is_guard; label = label} -> begin
is_guard
end))


let __proj__Mkgoal__item__label : goal  ->  Prims.string = (fun projectee -> (match (projectee) with
| {goal_main_env = goal_main_env; goal_ctx_uvar = goal_ctx_uvar; opts = opts; is_guard = is_guard; label = label} -> begin
label
end))


let goal_env : goal  ->  FStar_TypeChecker_Env.env = (fun g -> (

let uu___17_118 = g.goal_main_env
in {FStar_TypeChecker_Env.solver = uu___17_118.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___17_118.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___17_118.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = g.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___17_118.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___17_118.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___17_118.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___17_118.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___17_118.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___17_118.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___17_118.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___17_118.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___17_118.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___17_118.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___17_118.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___17_118.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___17_118.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___17_118.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___17_118.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___17_118.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___17_118.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___17_118.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___17_118.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___17_118.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___17_118.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___17_118.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___17_118.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___17_118.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___17_118.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___17_118.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___17_118.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___17_118.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___17_118.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___17_118.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___17_118.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___17_118.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___17_118.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___17_118.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___17_118.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___17_118.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___17_118.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___17_118.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___17_118.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___17_118.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___17_118.FStar_TypeChecker_Env.erasable_types_tab}))


let goal_witness : goal  ->  FStar_Syntax_Syntax.term = (fun g -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((g.goal_ctx_uvar), ((([]), (FStar_Syntax_Syntax.NoUseRange)))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let goal_type : goal  ->  FStar_Syntax_Syntax.term = (fun g -> g.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)


let goal_with_type : goal  ->  FStar_Syntax_Syntax.term  ->  goal = (fun g t -> (

let c = g.goal_ctx_uvar
in (

let c' = (

let uu___24_158 = c
in {FStar_Syntax_Syntax.ctx_uvar_head = uu___24_158.FStar_Syntax_Syntax.ctx_uvar_head; FStar_Syntax_Syntax.ctx_uvar_gamma = uu___24_158.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_Syntax_Syntax.ctx_uvar_binders = uu___24_158.FStar_Syntax_Syntax.ctx_uvar_binders; FStar_Syntax_Syntax.ctx_uvar_typ = t; FStar_Syntax_Syntax.ctx_uvar_reason = uu___24_158.FStar_Syntax_Syntax.ctx_uvar_reason; FStar_Syntax_Syntax.ctx_uvar_should_check = uu___24_158.FStar_Syntax_Syntax.ctx_uvar_should_check; FStar_Syntax_Syntax.ctx_uvar_range = uu___24_158.FStar_Syntax_Syntax.ctx_uvar_range; FStar_Syntax_Syntax.ctx_uvar_meta = uu___24_158.FStar_Syntax_Syntax.ctx_uvar_meta})
in (

let uu___27_159 = g
in {goal_main_env = uu___27_159.goal_main_env; goal_ctx_uvar = c'; opts = uu___27_159.opts; is_guard = uu___27_159.is_guard; label = uu___27_159.label}))))


let goal_with_env : goal  ->  FStar_TypeChecker_Env.env  ->  goal = (fun g env -> (

let c = g.goal_ctx_uvar
in (

let c' = (

let uu___32_173 = c
in (

let uu____174 = (FStar_TypeChecker_Env.all_binders env)
in {FStar_Syntax_Syntax.ctx_uvar_head = uu___32_173.FStar_Syntax_Syntax.ctx_uvar_head; FStar_Syntax_Syntax.ctx_uvar_gamma = env.FStar_TypeChecker_Env.gamma; FStar_Syntax_Syntax.ctx_uvar_binders = uu____174; FStar_Syntax_Syntax.ctx_uvar_typ = uu___32_173.FStar_Syntax_Syntax.ctx_uvar_typ; FStar_Syntax_Syntax.ctx_uvar_reason = uu___32_173.FStar_Syntax_Syntax.ctx_uvar_reason; FStar_Syntax_Syntax.ctx_uvar_should_check = uu___32_173.FStar_Syntax_Syntax.ctx_uvar_should_check; FStar_Syntax_Syntax.ctx_uvar_range = uu___32_173.FStar_Syntax_Syntax.ctx_uvar_range; FStar_Syntax_Syntax.ctx_uvar_meta = uu___32_173.FStar_Syntax_Syntax.ctx_uvar_meta}))
in (

let uu___35_183 = g
in {goal_main_env = env; goal_ctx_uvar = c'; opts = uu___35_183.opts; is_guard = uu___35_183.is_guard; label = uu___35_183.label}))))


let mk_goal : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Options.optionstate  ->  Prims.bool  ->  Prims.string  ->  goal = (fun env u o b l -> {goal_main_env = env; goal_ctx_uvar = u; opts = o; is_guard = b; label = l})


let rename_binders : 'Auu____221 . FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____221) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____221) Prims.list = (fun subst1 bs -> (FStar_All.pipe_right bs (FStar_List.map (fun uu___0_281 -> (match (uu___0_281) with
| (x, imp) -> begin
(

let y = (

let uu____293 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Subst.subst subst1 uu____293))
in (

let uu____294 = (

let uu____295 = (FStar_Syntax_Subst.compress y)
in uu____295.FStar_Syntax_Syntax.n)
in (match (uu____294) with
| FStar_Syntax_Syntax.Tm_name (y1) -> begin
(

let uu____303 = (

let uu___51_304 = y1
in (

let uu____305 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___51_304.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___51_304.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____305}))
in ((uu____303), (imp)))
end
| uu____308 -> begin
(failwith "Not a renaming")
end)))
end)))))


let subst_goal : FStar_Syntax_Syntax.subst_elt Prims.list  ->  goal  ->  goal = (fun subst1 goal -> (

let g = goal.goal_ctx_uvar
in (

let ctx_uvar = (

let uu___57_331 = g
in (

let uu____332 = (FStar_TypeChecker_Env.rename_gamma subst1 g.FStar_Syntax_Syntax.ctx_uvar_gamma)
in (

let uu____335 = (rename_binders subst1 g.FStar_Syntax_Syntax.ctx_uvar_binders)
in (

let uu____346 = (FStar_Syntax_Subst.subst subst1 g.FStar_Syntax_Syntax.ctx_uvar_typ)
in {FStar_Syntax_Syntax.ctx_uvar_head = uu___57_331.FStar_Syntax_Syntax.ctx_uvar_head; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____332; FStar_Syntax_Syntax.ctx_uvar_binders = uu____335; FStar_Syntax_Syntax.ctx_uvar_typ = uu____346; FStar_Syntax_Syntax.ctx_uvar_reason = uu___57_331.FStar_Syntax_Syntax.ctx_uvar_reason; FStar_Syntax_Syntax.ctx_uvar_should_check = uu___57_331.FStar_Syntax_Syntax.ctx_uvar_should_check; FStar_Syntax_Syntax.ctx_uvar_range = uu___57_331.FStar_Syntax_Syntax.ctx_uvar_range; FStar_Syntax_Syntax.ctx_uvar_meta = uu___57_331.FStar_Syntax_Syntax.ctx_uvar_meta}))))
in (

let uu___60_349 = goal
in {goal_main_env = uu___60_349.goal_main_env; goal_ctx_uvar = ctx_uvar; opts = uu___60_349.opts; is_guard = uu___60_349.is_guard; label = uu___60_349.label}))))

type guard_policy =
| Goal
| SMT
| Force
| Drop


let uu___is_Goal : guard_policy  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Goal -> begin
true
end
| uu____359 -> begin
false
end))


let uu___is_SMT : guard_policy  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SMT -> begin
true
end
| uu____370 -> begin
false
end))


let uu___is_Force : guard_policy  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Force -> begin
true
end
| uu____381 -> begin
false
end))


let uu___is_Drop : guard_policy  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Drop -> begin
true
end
| uu____392 -> begin
false
end))

type proofstate =
{main_context : FStar_TypeChecker_Env.env; all_implicits : FStar_TypeChecker_Env.implicits; goals : goal Prims.list; smt_goals : goal Prims.list; depth : Prims.int; __dump : proofstate  ->  Prims.string  ->  unit; psc : FStar_TypeChecker_Cfg.psc; entry_range : FStar_Range.range; guard_policy : guard_policy; freshness : Prims.int; tac_verb_dbg : Prims.bool; local_state : FStar_Syntax_Syntax.term FStar_Util.psmap}


let __proj__Mkproofstate__item__main_context : proofstate  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {main_context = main_context; all_implicits = all_implicits; goals = goals; smt_goals = smt_goals; depth = depth; __dump = __dump; psc = psc; entry_range = entry_range; guard_policy = guard_policy; freshness = freshness; tac_verb_dbg = tac_verb_dbg; local_state = local_state} -> begin
main_context
end))


let __proj__Mkproofstate__item__all_implicits : proofstate  ->  FStar_TypeChecker_Env.implicits = (fun projectee -> (match (projectee) with
| {main_context = main_context; all_implicits = all_implicits; goals = goals; smt_goals = smt_goals; depth = depth; __dump = __dump; psc = psc; entry_range = entry_range; guard_policy = guard_policy; freshness = freshness; tac_verb_dbg = tac_verb_dbg; local_state = local_state} -> begin
all_implicits
end))


let __proj__Mkproofstate__item__goals : proofstate  ->  goal Prims.list = (fun projectee -> (match (projectee) with
| {main_context = main_context; all_implicits = all_implicits; goals = goals; smt_goals = smt_goals; depth = depth; __dump = __dump; psc = psc; entry_range = entry_range; guard_policy = guard_policy; freshness = freshness; tac_verb_dbg = tac_verb_dbg; local_state = local_state} -> begin
goals
end))


let __proj__Mkproofstate__item__smt_goals : proofstate  ->  goal Prims.list = (fun projectee -> (match (projectee) with
| {main_context = main_context; all_implicits = all_implicits; goals = goals; smt_goals = smt_goals; depth = depth; __dump = __dump; psc = psc; entry_range = entry_range; guard_policy = guard_policy; freshness = freshness; tac_verb_dbg = tac_verb_dbg; local_state = local_state} -> begin
smt_goals
end))


let __proj__Mkproofstate__item__depth : proofstate  ->  Prims.int = (fun projectee -> (match (projectee) with
| {main_context = main_context; all_implicits = all_implicits; goals = goals; smt_goals = smt_goals; depth = depth; __dump = __dump; psc = psc; entry_range = entry_range; guard_policy = guard_policy; freshness = freshness; tac_verb_dbg = tac_verb_dbg; local_state = local_state} -> begin
depth
end))


let __proj__Mkproofstate__item____dump : proofstate  ->  proofstate  ->  Prims.string  ->  unit = (fun projectee -> (match (projectee) with
| {main_context = main_context; all_implicits = all_implicits; goals = goals; smt_goals = smt_goals; depth = depth; __dump = __dump; psc = psc; entry_range = entry_range; guard_policy = guard_policy; freshness = freshness; tac_verb_dbg = tac_verb_dbg; local_state = local_state} -> begin
__dump
end))


let __proj__Mkproofstate__item__psc : proofstate  ->  FStar_TypeChecker_Cfg.psc = (fun projectee -> (match (projectee) with
| {main_context = main_context; all_implicits = all_implicits; goals = goals; smt_goals = smt_goals; depth = depth; __dump = __dump; psc = psc; entry_range = entry_range; guard_policy = guard_policy; freshness = freshness; tac_verb_dbg = tac_verb_dbg; local_state = local_state} -> begin
psc
end))


let __proj__Mkproofstate__item__entry_range : proofstate  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {main_context = main_context; all_implicits = all_implicits; goals = goals; smt_goals = smt_goals; depth = depth; __dump = __dump; psc = psc; entry_range = entry_range; guard_policy = guard_policy; freshness = freshness; tac_verb_dbg = tac_verb_dbg; local_state = local_state} -> begin
entry_range
end))


let __proj__Mkproofstate__item__guard_policy : proofstate  ->  guard_policy = (fun projectee -> (match (projectee) with
| {main_context = main_context; all_implicits = all_implicits; goals = goals; smt_goals = smt_goals; depth = depth; __dump = __dump; psc = psc; entry_range = entry_range; guard_policy = guard_policy; freshness = freshness; tac_verb_dbg = tac_verb_dbg; local_state = local_state} -> begin
guard_policy
end))


let __proj__Mkproofstate__item__freshness : proofstate  ->  Prims.int = (fun projectee -> (match (projectee) with
| {main_context = main_context; all_implicits = all_implicits; goals = goals; smt_goals = smt_goals; depth = depth; __dump = __dump; psc = psc; entry_range = entry_range; guard_policy = guard_policy; freshness = freshness; tac_verb_dbg = tac_verb_dbg; local_state = local_state} -> begin
freshness
end))


let __proj__Mkproofstate__item__tac_verb_dbg : proofstate  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {main_context = main_context; all_implicits = all_implicits; goals = goals; smt_goals = smt_goals; depth = depth; __dump = __dump; psc = psc; entry_range = entry_range; guard_policy = guard_policy; freshness = freshness; tac_verb_dbg = tac_verb_dbg; local_state = local_state} -> begin
tac_verb_dbg
end))


let __proj__Mkproofstate__item__local_state : proofstate  ->  FStar_Syntax_Syntax.term FStar_Util.psmap = (fun projectee -> (match (projectee) with
| {main_context = main_context; all_implicits = all_implicits; goals = goals; smt_goals = smt_goals; depth = depth; __dump = __dump; psc = psc; entry_range = entry_range; guard_policy = guard_policy; freshness = freshness; tac_verb_dbg = tac_verb_dbg; local_state = local_state} -> begin
local_state
end))


let subst_proof_state : FStar_Syntax_Syntax.subst_t  ->  proofstate  ->  proofstate = (fun subst1 ps -> (

let uu____927 = (FStar_Options.tactic_raw_binders ())
in (match (uu____927) with
| true -> begin
ps
end
| uu____930 -> begin
(

let uu___101_932 = ps
in (

let uu____933 = (FStar_List.map (subst_goal subst1) ps.goals)
in {main_context = uu___101_932.main_context; all_implicits = uu___101_932.all_implicits; goals = uu____933; smt_goals = uu___101_932.smt_goals; depth = uu___101_932.depth; __dump = uu___101_932.__dump; psc = uu___101_932.psc; entry_range = uu___101_932.entry_range; guard_policy = uu___101_932.guard_policy; freshness = uu___101_932.freshness; tac_verb_dbg = uu___101_932.tac_verb_dbg; local_state = uu___101_932.local_state}))
end)))


let decr_depth : proofstate  ->  proofstate = (fun ps -> (

let uu___104_942 = ps
in {main_context = uu___104_942.main_context; all_implicits = uu___104_942.all_implicits; goals = uu___104_942.goals; smt_goals = uu___104_942.smt_goals; depth = (ps.depth - (Prims.parse_int "1")); __dump = uu___104_942.__dump; psc = uu___104_942.psc; entry_range = uu___104_942.entry_range; guard_policy = uu___104_942.guard_policy; freshness = uu___104_942.freshness; tac_verb_dbg = uu___104_942.tac_verb_dbg; local_state = uu___104_942.local_state}))


let incr_depth : proofstate  ->  proofstate = (fun ps -> (

let uu___107_950 = ps
in {main_context = uu___107_950.main_context; all_implicits = uu___107_950.all_implicits; goals = uu___107_950.goals; smt_goals = uu___107_950.smt_goals; depth = (ps.depth + (Prims.parse_int "1")); __dump = uu___107_950.__dump; psc = uu___107_950.psc; entry_range = uu___107_950.entry_range; guard_policy = uu___107_950.guard_policy; freshness = uu___107_950.freshness; tac_verb_dbg = uu___107_950.tac_verb_dbg; local_state = uu___107_950.local_state}))


let set_ps_psc : FStar_TypeChecker_Cfg.psc  ->  proofstate  ->  proofstate = (fun psc ps -> (

let uu___111_963 = ps
in {main_context = uu___111_963.main_context; all_implicits = uu___111_963.all_implicits; goals = uu___111_963.goals; smt_goals = uu___111_963.smt_goals; depth = uu___111_963.depth; __dump = uu___111_963.__dump; psc = psc; entry_range = uu___111_963.entry_range; guard_policy = uu___111_963.guard_policy; freshness = uu___111_963.freshness; tac_verb_dbg = uu___111_963.tac_verb_dbg; local_state = uu___111_963.local_state}))


let tracepoint : FStar_TypeChecker_Cfg.psc  ->  proofstate  ->  unit = (fun psc ps -> (

let uu____975 = ((FStar_Options.tactic_trace ()) || (

let uu____978 = (FStar_Options.tactic_trace_d ())
in (ps.depth <= uu____978)))
in (match (uu____975) with
| true -> begin
(

let ps1 = (set_ps_psc psc ps)
in (

let subst1 = (FStar_TypeChecker_Cfg.psc_subst ps1.psc)
in (

let uu____983 = (subst_proof_state subst1 ps1)
in (ps1.__dump uu____983 "TRACE"))))
end
| uu____985 -> begin
()
end)))


let set_proofstate_range : proofstate  ->  FStar_Range.range  ->  proofstate = (fun ps r -> (

let uu___120_998 = ps
in (

let uu____999 = (

let uu____1000 = (FStar_Range.def_range r)
in (FStar_Range.set_def_range ps.entry_range uu____1000))
in {main_context = uu___120_998.main_context; all_implicits = uu___120_998.all_implicits; goals = uu___120_998.goals; smt_goals = uu___120_998.smt_goals; depth = uu___120_998.depth; __dump = uu___120_998.__dump; psc = uu___120_998.psc; entry_range = uu____999; guard_policy = uu___120_998.guard_policy; freshness = uu___120_998.freshness; tac_verb_dbg = uu___120_998.tac_verb_dbg; local_state = uu___120_998.local_state})))


let goals_of : proofstate  ->  goal Prims.list = (fun ps -> ps.goals)


let smt_goals_of : proofstate  ->  goal Prims.list = (fun ps -> ps.smt_goals)


let is_guard : goal  ->  Prims.bool = (fun g -> g.is_guard)


let get_label : goal  ->  Prims.string = (fun g -> g.label)


let set_label : Prims.string  ->  goal  ->  goal = (fun l g -> (

let uu___128_1048 = g
in {goal_main_env = uu___128_1048.goal_main_env; goal_ctx_uvar = uu___128_1048.goal_ctx_uvar; opts = uu___128_1048.opts; is_guard = uu___128_1048.is_guard; label = l}))

type direction =
| TopDown
| BottomUp


let uu___is_TopDown : direction  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TopDown -> begin
true
end
| uu____1058 -> begin
false
end))


let uu___is_BottomUp : direction  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BottomUp -> begin
true
end
| uu____1069 -> begin
false
end))

exception TacticFailure of (Prims.string)


let uu___is_TacticFailure : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TacticFailure (uu____1084) -> begin
true
end
| uu____1087 -> begin
false
end))


let __proj__TacticFailure__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| TacticFailure (uu____1097) -> begin
uu____1097
end))

exception EExn of (FStar_Syntax_Syntax.term)


let uu___is_EExn : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EExn (uu____1111) -> begin
true
end
| uu____1113 -> begin
false
end))


let __proj__EExn__item__uu___ : Prims.exn  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| EExn (uu____1121) -> begin
uu____1121
end))




