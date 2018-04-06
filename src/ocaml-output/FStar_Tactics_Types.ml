
open Prims
open FStar_Pervasives
type goal =
{context : FStar_TypeChecker_Env.env; witness : FStar_Syntax_Syntax.term; goal_ty : FStar_Syntax_Syntax.typ; opts : FStar_Options.optionstate; is_guard : Prims.bool}


let __proj__Mkgoal__item__context : goal  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts; is_guard = __fname__is_guard} -> begin
__fname__context
end))


let __proj__Mkgoal__item__witness : goal  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts; is_guard = __fname__is_guard} -> begin
__fname__witness
end))


let __proj__Mkgoal__item__goal_ty : goal  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts; is_guard = __fname__is_guard} -> begin
__fname__goal_ty
end))


let __proj__Mkgoal__item__opts : goal  ->  FStar_Options.optionstate = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts; is_guard = __fname__is_guard} -> begin
__fname__opts
end))


let __proj__Mkgoal__item__is_guard : goal  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts; is_guard = __fname__is_guard} -> begin
__fname__is_guard
end))


let subst_goal : FStar_Syntax_Syntax.subst_t  ->  goal  ->  goal = (fun subst1 goal -> (

let uu___54_67 = goal
in (

let uu____68 = (FStar_TypeChecker_Env.rename_env subst1 goal.context)
in (

let uu____69 = (FStar_Syntax_Subst.subst subst1 goal.witness)
in (

let uu____70 = (FStar_Syntax_Subst.subst subst1 goal.goal_ty)
in {context = uu____68; witness = uu____69; goal_ty = uu____70; opts = uu___54_67.opts; is_guard = uu___54_67.is_guard})))))

type guard_policy =
| Goal
| SMT
| Force
| Drop


let uu___is_Goal : guard_policy  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Goal -> begin
true
end
| uu____74 -> begin
false
end))


let uu___is_SMT : guard_policy  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SMT -> begin
true
end
| uu____78 -> begin
false
end))


let uu___is_Force : guard_policy  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Force -> begin
true
end
| uu____82 -> begin
false
end))


let uu___is_Drop : guard_policy  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Drop -> begin
true
end
| uu____86 -> begin
false
end))

type proofstate =
{main_context : FStar_TypeChecker_Env.env; main_goal : goal; all_implicits : FStar_TypeChecker_Env.implicits; goals : goal Prims.list; smt_goals : goal Prims.list; depth : Prims.int; __dump : proofstate  ->  Prims.string  ->  Prims.unit; psc : FStar_TypeChecker_Normalize.psc; entry_range : FStar_Range.range; guard_policy : guard_policy; freshness : Prims.int}


let __proj__Mkproofstate__item__main_context : proofstate  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals; depth = __fname__depth; __dump = __fname____dump; psc = __fname__psc; entry_range = __fname__entry_range; guard_policy = __fname__guard_policy; freshness = __fname__freshness} -> begin
__fname__main_context
end))


let __proj__Mkproofstate__item__main_goal : proofstate  ->  goal = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals; depth = __fname__depth; __dump = __fname____dump; psc = __fname__psc; entry_range = __fname__entry_range; guard_policy = __fname__guard_policy; freshness = __fname__freshness} -> begin
__fname__main_goal
end))


let __proj__Mkproofstate__item__all_implicits : proofstate  ->  FStar_TypeChecker_Env.implicits = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals; depth = __fname__depth; __dump = __fname____dump; psc = __fname__psc; entry_range = __fname__entry_range; guard_policy = __fname__guard_policy; freshness = __fname__freshness} -> begin
__fname__all_implicits
end))


let __proj__Mkproofstate__item__goals : proofstate  ->  goal Prims.list = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals; depth = __fname__depth; __dump = __fname____dump; psc = __fname__psc; entry_range = __fname__entry_range; guard_policy = __fname__guard_policy; freshness = __fname__freshness} -> begin
__fname__goals
end))


let __proj__Mkproofstate__item__smt_goals : proofstate  ->  goal Prims.list = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals; depth = __fname__depth; __dump = __fname____dump; psc = __fname__psc; entry_range = __fname__entry_range; guard_policy = __fname__guard_policy; freshness = __fname__freshness} -> begin
__fname__smt_goals
end))


let __proj__Mkproofstate__item__depth : proofstate  ->  Prims.int = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals; depth = __fname__depth; __dump = __fname____dump; psc = __fname__psc; entry_range = __fname__entry_range; guard_policy = __fname__guard_policy; freshness = __fname__freshness} -> begin
__fname__depth
end))


let __proj__Mkproofstate__item____dump : proofstate  ->  proofstate  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals; depth = __fname__depth; __dump = __fname____dump; psc = __fname__psc; entry_range = __fname__entry_range; guard_policy = __fname__guard_policy; freshness = __fname__freshness} -> begin
__fname____dump
end))


let __proj__Mkproofstate__item__psc : proofstate  ->  FStar_TypeChecker_Normalize.psc = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals; depth = __fname__depth; __dump = __fname____dump; psc = __fname__psc; entry_range = __fname__entry_range; guard_policy = __fname__guard_policy; freshness = __fname__freshness} -> begin
__fname__psc
end))


let __proj__Mkproofstate__item__entry_range : proofstate  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals; depth = __fname__depth; __dump = __fname____dump; psc = __fname__psc; entry_range = __fname__entry_range; guard_policy = __fname__guard_policy; freshness = __fname__freshness} -> begin
__fname__entry_range
end))


let __proj__Mkproofstate__item__guard_policy : proofstate  ->  guard_policy = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals; depth = __fname__depth; __dump = __fname____dump; psc = __fname__psc; entry_range = __fname__entry_range; guard_policy = __fname__guard_policy; freshness = __fname__freshness} -> begin
__fname__guard_policy
end))


let __proj__Mkproofstate__item__freshness : proofstate  ->  Prims.int = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals; depth = __fname__depth; __dump = __fname____dump; psc = __fname__psc; entry_range = __fname__entry_range; guard_policy = __fname__guard_policy; freshness = __fname__freshness} -> begin
__fname__freshness
end))


let subst_proof_state : FStar_Syntax_Syntax.subst_t  ->  proofstate  ->  proofstate = (fun subst1 ps -> (

let uu____407 = (FStar_Options.tactic_raw_binders ())
in (match (uu____407) with
| true -> begin
ps
end
| uu____408 -> begin
(

let uu___55_409 = ps
in (

let uu____410 = (subst_goal subst1 ps.main_goal)
in (

let uu____411 = (FStar_List.map (subst_goal subst1) ps.goals)
in {main_context = uu___55_409.main_context; main_goal = uu____410; all_implicits = uu___55_409.all_implicits; goals = uu____411; smt_goals = uu___55_409.smt_goals; depth = uu___55_409.depth; __dump = uu___55_409.__dump; psc = uu___55_409.psc; entry_range = uu___55_409.entry_range; guard_policy = uu___55_409.guard_policy; freshness = uu___55_409.freshness})))
end)))


let decr_depth : proofstate  ->  proofstate = (fun ps -> (

let uu___56_417 = ps
in {main_context = uu___56_417.main_context; main_goal = uu___56_417.main_goal; all_implicits = uu___56_417.all_implicits; goals = uu___56_417.goals; smt_goals = uu___56_417.smt_goals; depth = (ps.depth - (Prims.parse_int "1")); __dump = uu___56_417.__dump; psc = uu___56_417.psc; entry_range = uu___56_417.entry_range; guard_policy = uu___56_417.guard_policy; freshness = uu___56_417.freshness}))


let incr_depth : proofstate  ->  proofstate = (fun ps -> (

let uu___57_421 = ps
in {main_context = uu___57_421.main_context; main_goal = uu___57_421.main_goal; all_implicits = uu___57_421.all_implicits; goals = uu___57_421.goals; smt_goals = uu___57_421.smt_goals; depth = (ps.depth + (Prims.parse_int "1")); __dump = uu___57_421.__dump; psc = uu___57_421.psc; entry_range = uu___57_421.entry_range; guard_policy = uu___57_421.guard_policy; freshness = uu___57_421.freshness}))


let tracepoint : proofstate  ->  Prims.unit = (fun ps -> (

let uu____425 = ((FStar_Options.tactic_trace ()) || (

let uu____427 = (FStar_Options.tactic_trace_d ())
in (ps.depth <= uu____427)))
in (match (uu____425) with
| true -> begin
(

let uu____428 = (

let uu____429 = (FStar_TypeChecker_Normalize.psc_subst ps.psc)
in (subst_proof_state uu____429 ps))
in (ps.__dump uu____428 "TRACE"))
end
| uu____430 -> begin
()
end)))


let set_ps_psc : FStar_TypeChecker_Normalize.psc  ->  proofstate  ->  proofstate = (fun psc ps -> (

let uu___58_437 = ps
in {main_context = uu___58_437.main_context; main_goal = uu___58_437.main_goal; all_implicits = uu___58_437.all_implicits; goals = uu___58_437.goals; smt_goals = uu___58_437.smt_goals; depth = uu___58_437.depth; __dump = uu___58_437.__dump; psc = psc; entry_range = uu___58_437.entry_range; guard_policy = uu___58_437.guard_policy; freshness = uu___58_437.freshness}))


let set_proofstate_range : proofstate  ->  FStar_Range.range  ->  proofstate = (fun ps r -> (

let uu___59_444 = ps
in {main_context = uu___59_444.main_context; main_goal = uu___59_444.main_goal; all_implicits = uu___59_444.all_implicits; goals = uu___59_444.goals; smt_goals = uu___59_444.smt_goals; depth = uu___59_444.depth; __dump = uu___59_444.__dump; psc = uu___59_444.psc; entry_range = r; guard_policy = uu___59_444.guard_policy; freshness = uu___59_444.freshness}))

type direction =
| TopDown
| BottomUp


let uu___is_TopDown : direction  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TopDown -> begin
true
end
| uu____448 -> begin
false
end))


let uu___is_BottomUp : direction  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BottomUp -> begin
true
end
| uu____452 -> begin
false
end))




