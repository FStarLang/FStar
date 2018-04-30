
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


let subst_goal : FStar_Syntax_Syntax.subst_elt Prims.list  ->  goal  ->  goal = (fun subst1 goal -> (

let uu___55_90 = goal
in (

let uu____91 = (FStar_TypeChecker_Env.rename_env subst1 goal.context)
in (

let uu____92 = (FStar_Syntax_Subst.subst subst1 goal.witness)
in (

let uu____93 = (FStar_Syntax_Subst.subst subst1 goal.goal_ty)
in {context = uu____91; witness = uu____92; goal_ty = uu____93; opts = uu___55_90.opts; is_guard = uu___55_90.is_guard})))))

type guard_policy =
| Goal
| SMT
| Force
| Drop


let uu___is_Goal : guard_policy  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Goal -> begin
true
end
| uu____99 -> begin
false
end))


let uu___is_SMT : guard_policy  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SMT -> begin
true
end
| uu____105 -> begin
false
end))


let uu___is_Force : guard_policy  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Force -> begin
true
end
| uu____111 -> begin
false
end))


let uu___is_Drop : guard_policy  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Drop -> begin
true
end
| uu____117 -> begin
false
end))

type proofstate =
{main_context : FStar_TypeChecker_Env.env; main_goal : goal; all_implicits : FStar_TypeChecker_Env.implicits; goals : goal Prims.list; smt_goals : goal Prims.list; depth : Prims.int; __dump : proofstate  ->  Prims.string  ->  unit; psc : FStar_TypeChecker_Normalize.psc; entry_range : FStar_Range.range; guard_policy : guard_policy; freshness : Prims.int}


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


let __proj__Mkproofstate__item____dump : proofstate  ->  proofstate  ->  Prims.string  ->  unit = (fun projectee -> (match (projectee) with
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

let uu____505 = (FStar_Options.tactic_raw_binders ())
in (match (uu____505) with
| true -> begin
ps
end
| uu____506 -> begin
(

let uu___56_507 = ps
in (

let uu____508 = (subst_goal subst1 ps.main_goal)
in (

let uu____509 = (FStar_List.map (subst_goal subst1) ps.goals)
in {main_context = uu___56_507.main_context; main_goal = uu____508; all_implicits = uu___56_507.all_implicits; goals = uu____509; smt_goals = uu___56_507.smt_goals; depth = uu___56_507.depth; __dump = uu___56_507.__dump; psc = uu___56_507.psc; entry_range = uu___56_507.entry_range; guard_policy = uu___56_507.guard_policy; freshness = uu___56_507.freshness})))
end)))


let decr_depth : proofstate  ->  proofstate = (fun ps -> (

let uu___57_517 = ps
in {main_context = uu___57_517.main_context; main_goal = uu___57_517.main_goal; all_implicits = uu___57_517.all_implicits; goals = uu___57_517.goals; smt_goals = uu___57_517.smt_goals; depth = (ps.depth - (Prims.parse_int "1")); __dump = uu___57_517.__dump; psc = uu___57_517.psc; entry_range = uu___57_517.entry_range; guard_policy = uu___57_517.guard_policy; freshness = uu___57_517.freshness}))


let incr_depth : proofstate  ->  proofstate = (fun ps -> (

let uu___58_523 = ps
in {main_context = uu___58_523.main_context; main_goal = uu___58_523.main_goal; all_implicits = uu___58_523.all_implicits; goals = uu___58_523.goals; smt_goals = uu___58_523.smt_goals; depth = (ps.depth + (Prims.parse_int "1")); __dump = uu___58_523.__dump; psc = uu___58_523.psc; entry_range = uu___58_523.entry_range; guard_policy = uu___58_523.guard_policy; freshness = uu___58_523.freshness}))


let tracepoint : proofstate  ->  unit = (fun ps -> (

let uu____529 = ((FStar_Options.tactic_trace ()) || (

let uu____531 = (FStar_Options.tactic_trace_d ())
in (ps.depth <= uu____531)))
in (match (uu____529) with
| true -> begin
(

let uu____532 = (

let uu____533 = (FStar_TypeChecker_Normalize.psc_subst ps.psc)
in (subst_proof_state uu____533 ps))
in (ps.__dump uu____532 "TRACE"))
end
| uu____534 -> begin
()
end)))


let set_ps_psc : FStar_TypeChecker_Normalize.psc  ->  proofstate  ->  proofstate = (fun psc ps -> (

let uu___59_545 = ps
in {main_context = uu___59_545.main_context; main_goal = uu___59_545.main_goal; all_implicits = uu___59_545.all_implicits; goals = uu___59_545.goals; smt_goals = uu___59_545.smt_goals; depth = uu___59_545.depth; __dump = uu___59_545.__dump; psc = psc; entry_range = uu___59_545.entry_range; guard_policy = uu___59_545.guard_policy; freshness = uu___59_545.freshness}))


let set_proofstate_range : proofstate  ->  FStar_Range.range  ->  proofstate = (fun ps r -> (

let uu___60_556 = ps
in {main_context = uu___60_556.main_context; main_goal = uu___60_556.main_goal; all_implicits = uu___60_556.all_implicits; goals = uu___60_556.goals; smt_goals = uu___60_556.smt_goals; depth = uu___60_556.depth; __dump = uu___60_556.__dump; psc = uu___60_556.psc; entry_range = r; guard_policy = uu___60_556.guard_policy; freshness = uu___60_556.freshness}))

type direction =
| TopDown
| BottomUp


let uu___is_TopDown : direction  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TopDown -> begin
true
end
| uu____562 -> begin
false
end))


let uu___is_BottomUp : direction  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BottomUp -> begin
true
end
| uu____568 -> begin
false
end))




