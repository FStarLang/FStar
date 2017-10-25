
open Prims
open FStar_Pervasives
type step =
| Beta
| Iota
| Zeta
| Exclude of step
| Weak
| HNF
| Primops
| Eager_unfolding
| Inlining
| NoDeltaSteps
| UnfoldUntil of FStar_Syntax_Syntax.delta_depth
| UnfoldOnly of FStar_Ident.lid Prims.list
| UnfoldTac
| PureSubtermsWithinComputations
| Simplify
| EraseUniverses
| AllowUnboundUniverses
| Reify
| CompressUvars
| NoFullNorm
| CheckNoUvars
| Unmeta


let uu___is_Beta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Beta -> begin
true
end
| uu____19 -> begin
false
end))


let uu___is_Iota : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iota -> begin
true
end
| uu____24 -> begin
false
end))


let uu___is_Zeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Zeta -> begin
true
end
| uu____29 -> begin
false
end))


let uu___is_Exclude : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
true
end
| uu____35 -> begin
false
end))


let __proj__Exclude__item___0 : step  ->  step = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
_0
end))


let uu___is_Weak : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Weak -> begin
true
end
| uu____48 -> begin
false
end))


let uu___is_HNF : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HNF -> begin
true
end
| uu____53 -> begin
false
end))


let uu___is_Primops : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____58 -> begin
false
end))


let uu___is_Eager_unfolding : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding -> begin
true
end
| uu____63 -> begin
false
end))


let uu___is_Inlining : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____68 -> begin
false
end))


let uu___is_NoDeltaSteps : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoDeltaSteps -> begin
true
end
| uu____73 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____79 -> begin
false
end))


let __proj__UnfoldUntil__item___0 : step  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
_0
end))


let uu___is_UnfoldOnly : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
true
end
| uu____95 -> begin
false
end))


let __proj__UnfoldOnly__item___0 : step  ->  FStar_Ident.lid Prims.list = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
_0
end))


let uu___is_UnfoldTac : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldTac -> begin
true
end
| uu____114 -> begin
false
end))


let uu___is_PureSubtermsWithinComputations : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PureSubtermsWithinComputations -> begin
true
end
| uu____119 -> begin
false
end))


let uu___is_Simplify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simplify -> begin
true
end
| uu____124 -> begin
false
end))


let uu___is_EraseUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EraseUniverses -> begin
true
end
| uu____129 -> begin
false
end))


let uu___is_AllowUnboundUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AllowUnboundUniverses -> begin
true
end
| uu____134 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____139 -> begin
false
end))


let uu___is_CompressUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CompressUvars -> begin
true
end
| uu____144 -> begin
false
end))


let uu___is_NoFullNorm : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoFullNorm -> begin
true
end
| uu____149 -> begin
false
end))


let uu___is_CheckNoUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckNoUvars -> begin
true
end
| uu____154 -> begin
false
end))


let uu___is_Unmeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unmeta -> begin
true
end
| uu____159 -> begin
false
end))


type steps =
step Prims.list

type psc =
{psc_range : FStar_Range.range; psc_subst : Prims.unit  ->  FStar_Syntax_Syntax.subst_t}


let __proj__Mkpsc__item__psc_range : psc  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {psc_range = __fname__psc_range; psc_subst = __fname__psc_subst} -> begin
__fname__psc_range
end))


let __proj__Mkpsc__item__psc_subst : psc  ->  Prims.unit  ->  FStar_Syntax_Syntax.subst_t = (fun projectee -> (match (projectee) with
| {psc_range = __fname__psc_range; psc_subst = __fname__psc_subst} -> begin
__fname__psc_subst
end))


let null_psc : psc = {psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____196 -> [])}


let psc_range : psc  ->  FStar_Range.range = (fun psc -> psc.psc_range)


let psc_subst : psc  ->  FStar_Syntax_Syntax.subst_t = (fun psc -> (psc.psc_subst ()))

type primitive_step =
{name : FStar_Ident.lid; arity : Prims.int; strong_reduction_ok : Prims.bool; requires_binder_substitution : Prims.bool; interpretation : psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option}


let __proj__Mkprimitive_step__item__name : primitive_step  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__name
end))


let __proj__Mkprimitive_step__item__arity : primitive_step  ->  Prims.int = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__arity
end))


let __proj__Mkprimitive_step__item__strong_reduction_ok : primitive_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__strong_reduction_ok
end))


let __proj__Mkprimitive_step__item__requires_binder_substitution : primitive_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__requires_binder_substitution
end))


let __proj__Mkprimitive_step__item__interpretation : primitive_step  ->  psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__interpretation
end))

type closure =
| Clos of ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
| Univ of FStar_Syntax_Syntax.universe
| Dummy


let uu___is_Clos : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Clos (_0) -> begin
true
end
| uu____403 -> begin
false
end))


let __proj__Clos__item___0 : closure  ->  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool) = (fun projectee -> (match (projectee) with
| Clos (_0) -> begin
_0
end))


let uu___is_Univ : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Univ (_0) -> begin
true
end
| uu____507 -> begin
false
end))


let __proj__Univ__item___0 : closure  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| Univ (_0) -> begin
_0
end))


let uu___is_Dummy : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Dummy -> begin
true
end
| uu____520 -> begin
false
end))


type env =
(FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list


let dummy : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) = ((FStar_Pervasives_Native.None), (Dummy))


let closure_to_string : closure  ->  Prims.string = (fun uu___178_540 -> (match (uu___178_540) with
| Clos (uu____541, t, uu____543, uu____544) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| Univ (uu____589) -> begin
"Univ"
end
| Dummy -> begin
"dummy"
end))

type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level Prims.list; primitive_steps : primitive_step Prims.list}


let __proj__Mkcfg__item__steps : cfg  ->  steps = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps} -> begin
__fname__steps
end))


let __proj__Mkcfg__item__tcenv : cfg  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps} -> begin
__fname__tcenv
end))


let __proj__Mkcfg__item__delta_level : cfg  ->  FStar_TypeChecker_Env.delta_level Prims.list = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps} -> begin
__fname__delta_level
end))


let __proj__Mkcfg__item__primitive_steps : cfg  ->  primitive_step Prims.list = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps} -> begin
__fname__primitive_steps
end))


let only_strong_steps' : primitive_step Prims.list  ->  primitive_step Prims.list = (fun steps -> (FStar_List.filter (fun ps -> ps.strong_reduction_ok) steps))


let only_strong_steps : cfg  ->  cfg = (fun cfg -> (

let uu___195_682 = cfg
in (

let uu____683 = (only_strong_steps' cfg.primitive_steps)
in {steps = uu___195_682.steps; tcenv = uu___195_682.tcenv; delta_level = uu___195_682.delta_level; primitive_steps = uu____683})))


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list

type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option * FStar_Range.range)
| App of (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range)
| Let of (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range)
| Steps of (steps * primitive_step Prims.list * FStar_TypeChecker_Env.delta_level Prims.list)
| Debug of (FStar_Syntax_Syntax.term * FStar_Util.time)


let uu___is_Arg : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Arg (_0) -> begin
true
end
| uu____830 -> begin
false
end))


let __proj__Arg__item___0 : stack_elt  ->  (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Arg (_0) -> begin
_0
end))


let uu___is_UnivArgs : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnivArgs (_0) -> begin
true
end
| uu____868 -> begin
false
end))


let __proj__UnivArgs__item___0 : stack_elt  ->  (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| UnivArgs (_0) -> begin
_0
end))


let uu___is_MemoLazy : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MemoLazy (_0) -> begin
true
end
| uu____906 -> begin
false
end))


let __proj__MemoLazy__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo = (fun projectee -> (match (projectee) with
| MemoLazy (_0) -> begin
_0
end))


let uu___is_Match : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Match (_0) -> begin
true
end
| uu____965 -> begin
false
end))


let __proj__Match__item___0 : stack_elt  ->  (env * branches * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Match (_0) -> begin
_0
end))


let uu___is_Abs : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Abs (_0) -> begin
true
end
| uu____1009 -> begin
false
end))


let __proj__Abs__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Abs (_0) -> begin
_0
end))


let uu___is_App : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| App (_0) -> begin
true
end
| uu____1067 -> begin
false
end))


let __proj__App__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| App (_0) -> begin
_0
end))


let uu___is_Meta : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
true
end
| uu____1109 -> begin
false
end))


let __proj__Meta__item___0 : stack_elt  ->  (FStar_Syntax_Syntax.metadata * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
_0
end))


let uu___is_Let : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
true
end
| uu____1143 -> begin
false
end))


let __proj__Let__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
_0
end))


let uu___is_Steps : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Steps (_0) -> begin
true
end
| uu____1191 -> begin
false
end))


let __proj__Steps__item___0 : stack_elt  ->  (steps * primitive_step Prims.list * FStar_TypeChecker_Env.delta_level Prims.list) = (fun projectee -> (match (projectee) with
| Steps (_0) -> begin
_0
end))


let uu___is_Debug : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
true
end
| uu____1239 -> begin
false
end))


let __proj__Debug__item___0 : stack_elt  ->  (FStar_Syntax_Syntax.term * FStar_Util.time) = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
_0
end))


type stack =
stack_elt Prims.list


let mk : 'Auu____1268 . 'Auu____1268  ->  FStar_Range.range  ->  'Auu____1268 FStar_Syntax_Syntax.syntax = (fun t r -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r))


let set_memo : 'a . 'a FStar_Syntax_Syntax.memo  ->  'a  ->  Prims.unit = (fun r t -> (

let uu____1319 = (FStar_ST.op_Bang r)
in (match (uu____1319) with
| FStar_Pervasives_Native.Some (uu____1386) -> begin
(failwith "Unexpected set_memo: thunk already evaluated")
end
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some (t)))
end)))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (

let uu____1459 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right uu____1459 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun uu___179_1467 -> (match (uu___179_1467) with
| Arg (c, uu____1469, uu____1470) -> begin
(

let uu____1471 = (closure_to_string c)
in (FStar_Util.format1 "Closure %s" uu____1471))
end
| MemoLazy (uu____1472) -> begin
"MemoLazy"
end
| Abs (uu____1479, bs, uu____1481, uu____1482, uu____1483) -> begin
(

let uu____1488 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" uu____1488))
end
| UnivArgs (uu____1493) -> begin
"UnivArgs"
end
| Match (uu____1500) -> begin
"Match"
end
| App (uu____1507, t, uu____1509, uu____1510) -> begin
(

let uu____1511 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "App %s" uu____1511))
end
| Meta (m, uu____1513) -> begin
"Meta"
end
| Let (uu____1514) -> begin
"Let"
end
| Steps (uu____1523, uu____1524, uu____1525) -> begin
"Steps"
end
| Debug (t, uu____1535) -> begin
(

let uu____1536 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Debug %s" uu____1536))
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (

let uu____1545 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right uu____1545 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> (

let uu____1563 = (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm")))
in (match (uu____1563) with
| true -> begin
(f ())
end
| uu____1564 -> begin
()
end)))


let log_primops : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> (

let uu____1578 = ((FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) || (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Primops"))))
in (match (uu____1578) with
| true -> begin
(f ())
end
| uu____1579 -> begin
()
end)))


let is_empty : 'Auu____1584 . 'Auu____1584 Prims.list  ->  Prims.bool = (fun uu___180_1590 -> (match (uu___180_1590) with
| [] -> begin
true
end
| uu____1593 -> begin
false
end))


let lookup_bvar : 'Auu____1604 'Auu____1605 . ('Auu____1605 * 'Auu____1604) Prims.list  ->  FStar_Syntax_Syntax.bv  ->  'Auu____1604 = (fun env x -> (FStar_All.try_with (fun uu___197_1628 -> (match (()) with
| () -> begin
(

let uu____1629 = (FStar_List.nth env x.FStar_Syntax_Syntax.index)
in (FStar_Pervasives_Native.snd uu____1629))
end)) (fun uu___196_1641 -> (match (uu___196_1641) with
| uu____1642 -> begin
(

let uu____1643 = (

let uu____1644 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" uu____1644))
in (failwith uu____1643))
end))))


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun l -> (match ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Pure_lid)
end
| uu____1653 -> begin
(match ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Tot_lid)
end
| uu____1656 -> begin
(match ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_PURE_lid)
end
| uu____1659 -> begin
FStar_Pervasives_Native.None
end)
end)
end))


let norm_universe : cfg  ->  env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us1 = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let uu____1685 = (FStar_List.fold_left (fun uu____1711 u1 -> (match (uu____1711) with
| (cur_kernel, cur_max, out) -> begin
(

let uu____1736 = (FStar_Syntax_Util.univ_kernel u1)
in (match (uu____1736) with
| (k_u, n1) -> begin
(

let uu____1751 = (FStar_Syntax_Util.eq_univs cur_kernel k_u)
in (match (uu____1751) with
| true -> begin
((cur_kernel), (u1), (out))
end
| uu____1762 -> begin
((k_u), (u1), ((cur_max)::out))
end))
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us1)
in (match (uu____1685) with
| (uu____1769, u1, out) -> begin
(FStar_List.rev ((u1)::out))
end))))
in (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(FStar_All.try_with (fun uu___199_1791 -> (match (()) with
| () -> begin
(

let uu____1794 = (

let uu____1795 = (FStar_List.nth env x)
in (FStar_Pervasives_Native.snd uu____1795))
in (match (uu____1794) with
| Univ (u3) -> begin
(aux u3)
end
| Dummy -> begin
(u2)::[]
end
| uu____1813 -> begin
(failwith "Impossible: universe variable bound to a term")
end))
end)) (fun uu___198_1819 -> (match (uu___198_1819) with
| uu____1822 -> begin
(

let uu____1823 = (FStar_All.pipe_right cfg.steps (FStar_List.contains AllowUnboundUniverses))
in (match (uu____1823) with
| true -> begin
(FStar_Syntax_Syntax.U_unknown)::[]
end
| uu____1826 -> begin
(failwith "Universe variable not found")
end))
end)))
end
| FStar_Syntax_Syntax.U_unif (uu____1829) when (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars)) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_zero -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_unif (uu____1838) -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_name (uu____1847) -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_unknown -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_max ([]) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let us1 = (

let uu____1854 = (FStar_List.collect aux us)
in (FStar_All.pipe_right uu____1854 norm_univs))
in (match (us1) with
| (u_k)::(hd1)::rest -> begin
(

let rest1 = (hd1)::rest
in (

let uu____1871 = (FStar_Syntax_Util.univ_kernel u_k)
in (match (uu____1871) with
| (FStar_Syntax_Syntax.U_zero, n1) -> begin
(

let uu____1879 = (FStar_All.pipe_right rest1 (FStar_List.for_all (fun u3 -> (

let uu____1887 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____1887) with
| (uu____1892, m) -> begin
(n1 <= m)
end)))))
in (match (uu____1879) with
| true -> begin
rest1
end
| uu____1896 -> begin
us1
end))
end
| uu____1897 -> begin
us1
end)))
end
| uu____1902 -> begin
us1
end))
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1906 = (aux u3)
in (FStar_List.map (fun _0_41 -> FStar_Syntax_Syntax.U_succ (_0_41)) uu____1906))
end)))
in (

let uu____1909 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____1909) with
| true -> begin
FStar_Syntax_Syntax.U_unknown
end
| uu____1910 -> begin
(

let uu____1911 = (aux u)
in (match (uu____1911) with
| [] -> begin
FStar_Syntax_Syntax.U_zero
end
| (FStar_Syntax_Syntax.U_zero)::[] -> begin
FStar_Syntax_Syntax.U_zero
end
| (FStar_Syntax_Syntax.U_zero)::(u1)::[] -> begin
u1
end
| (FStar_Syntax_Syntax.U_zero)::us -> begin
FStar_Syntax_Syntax.U_max (us)
end
| (u1)::[] -> begin
u1
end
| us -> begin
FStar_Syntax_Syntax.U_max (us)
end))
end)))))


let rec closure_as_term : cfg  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> ((log cfg (fun uu____2015 -> (

let uu____2016 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____2017 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2016 uu____2017)))));
(match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| uu____2024 -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2026) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t1
end
| FStar_Syntax_Syntax.Tm_constant (uu____2051) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_name (uu____2052) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2053) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2054) -> begin
(

let uu____2071 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____2071) with
| true -> begin
(

let uu____2072 = (

let uu____2073 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____2074 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s): CheckNoUvars: Unexpected unification variable remains: %s" uu____2073 uu____2074)))
in (failwith uu____2072))
end
| uu____2075 -> begin
t1
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____2077 = (

let uu____2078 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (uu____2078))
in (mk uu____2077 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let uu____2085 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2085))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____2087 = (lookup_bvar env x)
in (match (uu____2087) with
| Univ (uu____2090) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t1
end
| Clos (env1, t0, r, uu____2094) -> begin
(closure_as_term cfg env1 t0)
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (closure_as_term_delayed cfg env head1)
in (

let args1 = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app (((head2), (args1)))) t1.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let uu____2206 = (closures_as_binders_delayed cfg env bs)
in (match (uu____2206) with
| (bs1, env1) -> begin
(

let body1 = (closure_as_term_delayed cfg env1 body)
in (

let uu____2234 = (

let uu____2235 = (

let uu____2252 = (close_lcomp_opt cfg env1 lopt)
in ((bs1), (body1), (uu____2252)))
in FStar_Syntax_Syntax.Tm_abs (uu____2235))
in (mk uu____2234 t1.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____2283 = (closures_as_binders_delayed cfg env bs)
in (match (uu____2283) with
| (bs1, env1) -> begin
(

let c1 = (close_comp cfg env1 c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs1), (c1)))) t1.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____2325 = (

let uu____2336 = (

let uu____2343 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2343)::[])
in (closures_as_binders_delayed cfg env uu____2336))
in (match (uu____2325) with
| (x1, env1) -> begin
(

let phi1 = (closure_as_term_delayed cfg env1 phi)
in (

let uu____2361 = (

let uu____2362 = (

let uu____2369 = (

let uu____2370 = (FStar_List.hd x1)
in (FStar_All.pipe_right uu____2370 FStar_Pervasives_Native.fst))
in ((uu____2369), (phi1)))
in FStar_Syntax_Syntax.Tm_refine (uu____2362))
in (mk uu____2361 t1.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (annot, tacopt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____2461 = (closure_as_term_delayed cfg env t2)
in FStar_Util.Inl (uu____2461))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2475 = (close_comp cfg env c)
in FStar_Util.Inr (uu____2475))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (closure_as_term_delayed cfg env))
in (

let uu____2491 = (

let uu____2492 = (

let uu____2519 = (closure_as_term_delayed cfg env t11)
in ((uu____2519), (((annot1), (tacopt1))), (lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2492))
in (mk uu____2491 t1.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____2570 = (

let uu____2571 = (

let uu____2578 = (closure_as_term_delayed cfg env t')
in (

let uu____2581 = (

let uu____2582 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (uu____2582))
in ((uu____2578), (uu____2581))))
in FStar_Syntax_Syntax.Tm_meta (uu____2571))
in (mk uu____2570 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(

let uu____2642 = (

let uu____2643 = (

let uu____2650 = (closure_as_term_delayed cfg env t')
in (

let uu____2653 = (

let uu____2654 = (

let uu____2661 = (closure_as_term_delayed cfg env tbody)
in ((m), (uu____2661)))
in FStar_Syntax_Syntax.Meta_monadic (uu____2654))
in ((uu____2650), (uu____2653))))
in FStar_Syntax_Syntax.Tm_meta (uu____2643))
in (mk uu____2642 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody)) -> begin
(

let uu____2680 = (

let uu____2681 = (

let uu____2688 = (closure_as_term_delayed cfg env t')
in (

let uu____2691 = (

let uu____2692 = (

let uu____2701 = (closure_as_term_delayed cfg env tbody)
in ((m1), (m2), (uu____2701)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____2692))
in ((uu____2688), (uu____2691))))
in FStar_Syntax_Syntax.Tm_meta (uu____2681))
in (mk uu____2680 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(

let uu____2714 = (

let uu____2715 = (

let uu____2722 = (closure_as_term_delayed cfg env t')
in ((uu____2722), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____2715))
in (mk uu____2714 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env1 = (FStar_List.fold_left (fun env1 uu____2762 -> (dummy)::env1) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____2781 = (

let uu____2792 = (FStar_Syntax_Syntax.is_top_level ((lb)::[]))
in (match (uu____2792) with
| true -> begin
((lb.FStar_Syntax_Syntax.lbname), (body))
end
| uu____2809 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2811 = (closure_as_term cfg ((dummy)::env0) body)
in ((FStar_Util.Inl ((

let uu___200_2823 = x
in {FStar_Syntax_Syntax.ppname = uu___200_2823.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___200_2823.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = typ}))), (uu____2811))))
end))
in (match (uu____2781) with
| (nm, body1) -> begin
(

let lb1 = (

let uu___201_2839 = lb
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___201_2839.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = uu___201_2839.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (body1)))) t1.FStar_Syntax_Syntax.pos))
end))))))
end
| FStar_Syntax_Syntax.Tm_let ((uu____2850, lbs), body) -> begin
(

let norm_one_lb = (fun env1 lb -> (

let env_univs = (FStar_List.fold_right (fun uu____2909 env2 -> (dummy)::env2) lb.FStar_Syntax_Syntax.lbunivs env1)
in (

let env2 = (

let uu____2934 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____2934) with
| true -> begin
env_univs
end
| uu____2943 -> begin
(FStar_List.fold_right (fun uu____2954 env2 -> (dummy)::env2) lbs env_univs)
end))
in (

let ty = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (

let nm = (

let uu____2976 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____2976) with
| true -> begin
lb.FStar_Syntax_Syntax.lbname
end
| uu____2981 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_All.pipe_right (

let uu___202_2988 = x
in {FStar_Syntax_Syntax.ppname = uu___202_2988.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___202_2988.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty}) (fun _0_42 -> FStar_Util.Inl (_0_42))))
end))
in (

let uu___203_2989 = lb
in (

let uu____2990 = (closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___203_2989.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___203_2989.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____2990})))))))
in (

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body1 = (

let body_env = (FStar_List.fold_right (fun uu____3020 env1 -> (dummy)::env1) lbs1 env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs1))), (body1)))) t1.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let head2 = (closure_as_term cfg env head1)
in (

let norm_one_branch = (fun env1 uu____3109 -> (match (uu____3109) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____3164) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3185 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____3245 uu____3246 -> (match (((uu____3245), (uu____3246))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____3337 = (norm_pat env3 p1)
in (match (uu____3337) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____3185) with
| (pats1, env3) -> begin
(((

let uu___204_3419 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___204_3419.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___205_3438 = x
in (

let uu____3439 = (closure_as_term cfg env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___205_3438.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___205_3438.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3439}))
in (((

let uu___206_3453 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___206_3453.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___207_3464 = x
in (

let uu____3465 = (closure_as_term cfg env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___207_3464.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___207_3464.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3465}))
in (((

let uu___208_3479 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___208_3479.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t2) -> begin
(

let x1 = (

let uu___209_3495 = x
in (

let uu____3496 = (closure_as_term cfg env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___209_3495.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___209_3495.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3496}))
in (

let t3 = (closure_as_term cfg env2 t2)
in (((

let uu___210_3503 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t3))); FStar_Syntax_Syntax.p = uu___210_3503.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let uu____3506 = (norm_pat env1 pat)
in (match (uu____3506) with
| (pat1, env2) -> begin
(

let w_opt1 = (match (w_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____3535 = (closure_as_term cfg env2 w)
in FStar_Pervasives_Native.Some (uu____3535))
end)
in (

let tm1 = (closure_as_term cfg env2 tm)
in ((pat1), (w_opt1), (tm1))))
end)))
end))
in (

let uu____3541 = (

let uu____3542 = (

let uu____3565 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head2), (uu____3565)))
in FStar_Syntax_Syntax.Tm_match (uu____3542))
in (mk uu____3541 t1.FStar_Syntax_Syntax.pos))))
end))
end);
))
and closure_as_term_delayed : cfg  ->  env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| uu____3651 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| uu____3677 -> begin
(FStar_List.map (fun uu____3694 -> (match (uu____3694) with
| (x, imp) -> begin
(

let uu____3713 = (closure_as_term_delayed cfg env x)
in ((uu____3713), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * env) = (fun cfg env bs -> (

let uu____3727 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____3776 uu____3777 -> (match (((uu____3776), (uu____3777))) with
| ((env1, out), (b, imp)) -> begin
(

let b1 = (

let uu___211_3847 = b
in (

let uu____3848 = (closure_as_term_delayed cfg env1 b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___211_3847.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___211_3847.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3848}))
in (

let env2 = (dummy)::env1
in ((env2), ((((b1), (imp)))::out))))
end)) ((env), ([]))))
in (match (uu____3727) with
| (env1, bs1) -> begin
(((FStar_List.rev bs1)), (env1))
end)))
and close_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| uu____3941 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____3954 = (closure_as_term_delayed cfg env t)
in (

let uu____3955 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____3954 uu____3955)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____3968 = (closure_as_term_delayed cfg env t)
in (

let uu____3969 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____3968 uu____3969)))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let rt = (closure_as_term_delayed cfg env c1.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c1.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___181_3995 -> (match (uu___181_3995) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____3999 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (uu____3999))
end
| f -> begin
f
end))))
in (

let uu____4003 = (

let uu___212_4004 = c1
in (

let uu____4005 = (FStar_List.map (norm_universe cfg env) c1.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = uu____4005; FStar_Syntax_Syntax.effect_name = uu___212_4004.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp uu____4003)))))
end)
end))
and filter_out_lcomp_cflags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun flags -> (FStar_All.pipe_right flags (FStar_List.filter (fun uu___182_4015 -> (match (uu___182_4015) with
| FStar_Syntax_Syntax.DECREASES (uu____4016) -> begin
false
end
| uu____4019 -> begin
true
end)))))
and close_lcomp_opt : cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.filter (fun uu___183_4037 -> (match (uu___183_4037) with
| FStar_Syntax_Syntax.DECREASES (uu____4038) -> begin
false
end
| uu____4041 -> begin
true
end))))
in (

let rc1 = (

let uu___213_4043 = rc
in (

let uu____4044 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (closure_as_term cfg env))
in {FStar_Syntax_Syntax.residual_effect = uu___213_4043.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____4044; FStar_Syntax_Syntax.residual_flags = flags}))
in FStar_Pervasives_Native.Some (rc1)))
end
| uu____4051 -> begin
lopt
end))


let built_in_primitive_steps : primitive_step Prims.list = (

let arg_as_int = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) FStar_Syntax_Embeddings.unembed_int_safe))
in (

let arg_as_bool = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) FStar_Syntax_Embeddings.unembed_bool_safe))
in (

let arg_as_char = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) FStar_Syntax_Embeddings.unembed_char_safe))
in (

let arg_as_string = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) FStar_Syntax_Embeddings.unembed_string_safe))
in (

let arg_as_list = (fun u a -> (

let uu____4139 = (FStar_Syntax_Embeddings.unembed_list_safe u)
in (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4139)))
in (

let arg_as_bounded_int = (fun uu____4167 -> (match (uu____4167) with
| (a, uu____4179) -> begin
(

let uu____4186 = (

let uu____4187 = (FStar_Syntax_Subst.compress a)
in uu____4187.FStar_Syntax_Syntax.n)
in (match (uu____4186) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv1); FStar_Syntax_Syntax.pos = uu____4197; FStar_Syntax_Syntax.vars = uu____4198}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, FStar_Pervasives_Native.None)); FStar_Syntax_Syntax.pos = uu____4200; FStar_Syntax_Syntax.vars = uu____4201}, uu____4202))::[]) when (FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") -> begin
(

let uu____4241 = (

let uu____4246 = (FStar_BigInt.big_int_of_string i)
in ((fv1), (uu____4246)))
in FStar_Pervasives_Native.Some (uu____4241))
end
| uu____4251 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let lift_unary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a))::[] -> begin
(

let uu____4293 = (f a)
in FStar_Pervasives_Native.Some (uu____4293))
end
| uu____4294 -> begin
FStar_Pervasives_Native.None
end))
in (

let lift_binary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a0))::(FStar_Pervasives_Native.Some (a1))::[] -> begin
(

let uu____4344 = (f a0 a1)
in FStar_Pervasives_Native.Some (uu____4344))
end
| uu____4345 -> begin
FStar_Pervasives_Native.None
end))
in (

let unary_op = (fun as_a f res args -> (

let uu____4394 = (FStar_List.map as_a args)
in (lift_unary (f res.psc_range) uu____4394)))
in (

let binary_op = (fun as_a f res args -> (

let uu____4450 = (FStar_List.map as_a args)
in (lift_binary (f res.psc_range) uu____4450)))
in (

let as_primitive_step = (fun uu____4474 -> (match (uu____4474) with
| (l, arity, f) -> begin
{name = l; arity = arity; strong_reduction_ok = true; requires_binder_substitution = false; interpretation = f}
end))
in (

let unary_int_op = (fun f -> (unary_op arg_as_int (fun r x -> (

let uu____4522 = (f x)
in (FStar_Syntax_Embeddings.embed_int r uu____4522)))))
in (

let binary_int_op = (fun f -> (binary_op arg_as_int (fun r x y -> (

let uu____4550 = (f x y)
in (FStar_Syntax_Embeddings.embed_int r uu____4550)))))
in (

let unary_bool_op = (fun f -> (unary_op arg_as_bool (fun r x -> (

let uu____4571 = (f x)
in (FStar_Syntax_Embeddings.embed_bool r uu____4571)))))
in (

let binary_bool_op = (fun f -> (binary_op arg_as_bool (fun r x y -> (

let uu____4599 = (f x y)
in (FStar_Syntax_Embeddings.embed_bool r uu____4599)))))
in (

let binary_string_op = (fun f -> (binary_op arg_as_string (fun r x y -> (

let uu____4627 = (f x y)
in (FStar_Syntax_Embeddings.embed_string r uu____4627)))))
in (

let list_of_string' = (fun rng s -> (

let name = (fun l -> (

let uu____4641 = (

let uu____4642 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____4642))
in (mk uu____4641 rng)))
in (

let char_t = (name FStar_Parser_Const.char_lid)
in (

let charterm = (fun c -> (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))) rng))
in (

let uu____4652 = (

let uu____4655 = (FStar_String.list_of_string s)
in (FStar_List.map charterm uu____4655))
in (FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4652))))))
in (

let string_of_list' = (fun rng l -> (

let s = (FStar_String.string_of_list l)
in (FStar_Syntax_Util.exp_string s)))
in (

let string_compare' = (fun rng s1 s2 -> (

let r = (FStar_String.compare s1 s2)
in (

let uu____4685 = (

let uu____4686 = (FStar_Util.string_of_int r)
in (FStar_BigInt.big_int_of_string uu____4686))
in (FStar_Syntax_Embeddings.embed_int rng uu____4685))))
in (

let string_concat' = (fun psc args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____4704 = (arg_as_string a1)
in (match (uu____4704) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____4710 = (arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2)
in (match (uu____4710) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.concat s1 s2)
in (

let uu____4723 = (FStar_Syntax_Embeddings.embed_string psc.psc_range r)
in FStar_Pervasives_Native.Some (uu____4723)))
end
| uu____4724 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4729 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4732 -> begin
FStar_Pervasives_Native.None
end))
in (

let string_of_int1 = (fun rng i -> (

let uu____4742 = (FStar_BigInt.string_of_big_int i)
in (FStar_Syntax_Embeddings.embed_string rng uu____4742)))
in (

let string_of_bool1 = (fun rng b -> (FStar_Syntax_Embeddings.embed_string rng (match (b) with
| true -> begin
"true"
end
| uu____4750 -> begin
"false"
end)))
in (

let term_of_range = (fun r -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r))) FStar_Pervasives_Native.None r))
in (

let range_of1 = (fun uu____4772 args -> (match (args) with
| (uu____4784)::((t, uu____4786))::[] -> begin
(

let uu____4815 = (term_of_range t.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (uu____4815))
end
| uu____4820 -> begin
FStar_Pervasives_Native.None
end))
in (

let set_range_of1 = (fun uu____4842 args -> (match (args) with
| (uu____4852)::((t, uu____4854))::((r, uu____4856))::[] -> begin
(

let uu____4877 = (FStar_Syntax_Embeddings.unembed_range_safe r)
in (FStar_Util.bind_opt uu____4877 (fun r1 -> FStar_Pervasives_Native.Some ((

let uu___214_4887 = t
in {FStar_Syntax_Syntax.n = uu___214_4887.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___214_4887.FStar_Syntax_Syntax.vars})))))
end
| uu____4888 -> begin
FStar_Pervasives_Native.None
end))
in (

let mk_range1 = (fun uu____4904 args -> (match (args) with
| (fn)::(from_line)::(from_col)::(to_line)::(to_col)::[] -> begin
(

let uu____4915 = (

let uu____4936 = (arg_as_string fn)
in (

let uu____4939 = (arg_as_int from_line)
in (

let uu____4942 = (arg_as_int from_col)
in (

let uu____4945 = (arg_as_int to_line)
in (

let uu____4948 = (arg_as_int to_col)
in ((uu____4936), (uu____4939), (uu____4942), (uu____4945), (uu____4948)))))))
in (match (uu____4915) with
| (FStar_Pervasives_Native.Some (fn1), FStar_Pervasives_Native.Some (from_l), FStar_Pervasives_Native.Some (from_c), FStar_Pervasives_Native.Some (to_l), FStar_Pervasives_Native.Some (to_c)) -> begin
(

let r = (

let uu____4979 = (

let uu____4980 = (FStar_BigInt.to_int_fs from_l)
in (

let uu____4981 = (FStar_BigInt.to_int_fs from_c)
in (FStar_Range.mk_pos uu____4980 uu____4981)))
in (

let uu____4982 = (

let uu____4983 = (FStar_BigInt.to_int_fs to_l)
in (

let uu____4984 = (FStar_BigInt.to_int_fs to_c)
in (FStar_Range.mk_pos uu____4983 uu____4984)))
in (FStar_Range.mk_range fn1 uu____4979 uu____4982)))
in (

let uu____4985 = (term_of_range r)
in FStar_Pervasives_Native.Some (uu____4985)))
end
| uu____4990 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____5011 -> begin
FStar_Pervasives_Native.None
end))
in (

let decidable_eq = (fun neg psc args -> (

let r = psc.psc_range
in (

let tru = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) r)
in (

let fal = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) r)
in (match (args) with
| ((_typ, uu____5038))::((a1, uu____5040))::((a2, uu____5042))::[] -> begin
(

let uu____5079 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____5079) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
fal
end
| uu____5086 -> begin
tru
end))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
tru
end
| uu____5091 -> begin
fal
end))
end
| uu____5092 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____5093 -> begin
(failwith "Unexpected number of arguments")
end)))))
in (

let basic_ops = (

let uu____5111 = (

let uu____5126 = (

let uu____5141 = (

let uu____5156 = (

let uu____5171 = (

let uu____5186 = (

let uu____5201 = (

let uu____5216 = (

let uu____5231 = (

let uu____5246 = (

let uu____5261 = (

let uu____5276 = (

let uu____5291 = (

let uu____5306 = (

let uu____5321 = (

let uu____5336 = (

let uu____5351 = (

let uu____5366 = (

let uu____5381 = (

let uu____5396 = (

let uu____5409 = (FStar_Parser_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((uu____5409), ((Prims.parse_int "1")), ((unary_op arg_as_string list_of_string'))))
in (

let uu____5416 = (

let uu____5431 = (

let uu____5444 = (FStar_Parser_Const.p2l (("FStar")::("String")::("string_of_list")::[]))
in ((uu____5444), ((Prims.parse_int "1")), ((unary_op (arg_as_list FStar_Syntax_Embeddings.unembed_char_safe) string_of_list'))))
in (

let uu____5453 = (

let uu____5468 = (

let uu____5483 = (FStar_Parser_Const.p2l (("FStar")::("String")::("concat")::[]))
in ((uu____5483), ((Prims.parse_int "2")), (string_concat')))
in (

let uu____5492 = (

let uu____5509 = (

let uu____5530 = (FStar_Parser_Const.p2l (("Prims")::("range_of")::[]))
in ((uu____5530), ((Prims.parse_int "2")), (range_of1)))
in (

let uu____5545 = (

let uu____5568 = (

let uu____5587 = (FStar_Parser_Const.p2l (("Prims")::("set_range_of")::[]))
in ((uu____5587), ((Prims.parse_int "3")), (set_range_of1)))
in (

let uu____5600 = (

let uu____5621 = (

let uu____5636 = (FStar_Parser_Const.p2l (("Prims")::("mk_range")::[]))
in ((uu____5636), ((Prims.parse_int "5")), (mk_range1)))
in (uu____5621)::[])
in (uu____5568)::uu____5600))
in (uu____5509)::uu____5545))
in (uu____5468)::uu____5492))
in (uu____5431)::uu____5453))
in (uu____5396)::uu____5416))
in (((FStar_Parser_Const.op_notEq), ((Prims.parse_int "3")), ((decidable_eq true))))::uu____5381)
in (((FStar_Parser_Const.op_Eq), ((Prims.parse_int "3")), ((decidable_eq false))))::uu____5366)
in (((FStar_Parser_Const.string_compare), ((Prims.parse_int "2")), ((binary_op arg_as_string string_compare'))))::uu____5351)
in (((FStar_Parser_Const.string_of_bool_lid), ((Prims.parse_int "1")), ((unary_op arg_as_bool string_of_bool1))))::uu____5336)
in (((FStar_Parser_Const.string_of_int_lid), ((Prims.parse_int "1")), ((unary_op arg_as_int string_of_int1))))::uu____5321)
in (((FStar_Parser_Const.strcat_lid'), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____5306)
in (((FStar_Parser_Const.strcat_lid), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____5291)
in (((FStar_Parser_Const.op_Or), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x || y))))))::uu____5276)
in (((FStar_Parser_Const.op_And), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x && y))))))::uu____5261)
in (((FStar_Parser_Const.op_Modulus), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.mod_big_int x y))))))::uu____5246)
in (((FStar_Parser_Const.op_GTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (

let uu____5984 = (FStar_BigInt.ge_big_int x y)
in (FStar_Syntax_Embeddings.embed_bool r uu____5984)))))))::uu____5231)
in (((FStar_Parser_Const.op_GT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (

let uu____6010 = (FStar_BigInt.gt_big_int x y)
in (FStar_Syntax_Embeddings.embed_bool r uu____6010)))))))::uu____5216)
in (((FStar_Parser_Const.op_LTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (

let uu____6036 = (FStar_BigInt.le_big_int x y)
in (FStar_Syntax_Embeddings.embed_bool r uu____6036)))))))::uu____5201)
in (((FStar_Parser_Const.op_LT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (

let uu____6062 = (FStar_BigInt.lt_big_int x y)
in (FStar_Syntax_Embeddings.embed_bool r uu____6062)))))))::uu____5186)
in (((FStar_Parser_Const.op_Division), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.div_big_int x y))))))::uu____5171)
in (((FStar_Parser_Const.op_Multiply), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.mult_big_int x y))))))::uu____5156)
in (((FStar_Parser_Const.op_Subtraction), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.sub_big_int x y))))))::uu____5141)
in (((FStar_Parser_Const.op_Addition), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.add_big_int x y))))))::uu____5126)
in (((FStar_Parser_Const.op_Minus), ((Prims.parse_int "1")), ((unary_int_op (fun x -> (FStar_BigInt.minus_big_int x))))))::uu____5111)
in (

let bounded_arith_ops = (

let bounded_int_types = ("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]
in (

let int_as_bounded = (fun r int_to_t1 n1 -> (

let c = (FStar_Syntax_Embeddings.embed_int r n1)
in (

let int_to_t2 = (FStar_Syntax_Syntax.fv_to_tm int_to_t1)
in (

let uu____6212 = (

let uu____6213 = (

let uu____6214 = (FStar_Syntax_Syntax.as_arg c)
in (uu____6214)::[])
in (FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6213))
in (uu____6212 FStar_Pervasives_Native.None r)))))
in (FStar_All.pipe_right bounded_int_types (FStar_List.collect (fun m -> (

let uu____6249 = (

let uu____6262 = (FStar_Parser_Const.p2l (("FStar")::(m)::("add")::[]))
in ((uu____6262), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____6282 uu____6283 -> (match (((uu____6282), (uu____6283))) with
| ((int_to_t1, x), (uu____6302, y)) -> begin
(

let uu____6312 = (FStar_BigInt.add_big_int x y)
in (int_as_bounded r int_to_t1 uu____6312))
end))))))
in (

let uu____6313 = (

let uu____6328 = (

let uu____6341 = (FStar_Parser_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((uu____6341), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____6361 uu____6362 -> (match (((uu____6361), (uu____6362))) with
| ((int_to_t1, x), (uu____6381, y)) -> begin
(

let uu____6391 = (FStar_BigInt.sub_big_int x y)
in (int_as_bounded r int_to_t1 uu____6391))
end))))))
in (

let uu____6392 = (

let uu____6407 = (

let uu____6420 = (FStar_Parser_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((uu____6420), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____6440 uu____6441 -> (match (((uu____6440), (uu____6441))) with
| ((int_to_t1, x), (uu____6460, y)) -> begin
(

let uu____6470 = (FStar_BigInt.mult_big_int x y)
in (int_as_bounded r int_to_t1 uu____6470))
end))))))
in (uu____6407)::[])
in (uu____6328)::uu____6392))
in (uu____6249)::uu____6313)))))))
in (FStar_List.map as_primitive_step (FStar_List.append basic_ops bounded_arith_ops)))))))))))))))))))))))))))))))


let equality_ops : primitive_step Prims.list = (

let interp_prop = (fun psc args -> (

let r = psc.psc_range
in (match (args) with
| ((_typ, uu____6560))::((a1, uu____6562))::((a2, uu____6564))::[] -> begin
(

let uu____6601 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____6601) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___215_6607 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___215_6607.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___215_6607.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___216_6611 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___216_6611.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___216_6611.FStar_Syntax_Syntax.vars}))
end
| uu____6612 -> begin
FStar_Pervasives_Native.None
end))
end
| ((_typ, uu____6614))::(uu____6615)::((a1, uu____6617))::((a2, uu____6619))::[] -> begin
(

let uu____6668 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____6668) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___215_6674 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___215_6674.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___215_6674.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___216_6678 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___216_6678.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___216_6678.FStar_Syntax_Syntax.vars}))
end
| uu____6679 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____6680 -> begin
(failwith "Unexpected number of arguments")
end)))
in (

let propositional_equality = {name = FStar_Parser_Const.eq2_lid; arity = (Prims.parse_int "3"); strong_reduction_ok = true; requires_binder_substitution = false; interpretation = interp_prop}
in (

let hetero_propositional_equality = {name = FStar_Parser_Const.eq3_lid; arity = (Prims.parse_int "4"); strong_reduction_ok = true; requires_binder_substitution = false; interpretation = interp_prop}
in (propositional_equality)::(hetero_propositional_equality)::[])))


let unembed_binder : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option = (fun t -> (FStar_All.try_with (fun uu___218_6697 -> (match (()) with
| () -> begin
(

let uu____6700 = (

let uu____6701 = (FStar_Syntax_Util.un_alien t)
in (FStar_All.pipe_right uu____6701 FStar_Dyn.undyn))
in FStar_Pervasives_Native.Some (uu____6700))
end)) (fun uu___217_6704 -> (match (uu___217_6704) with
| uu____6707 -> begin
FStar_Pervasives_Native.None
end))))


let mk_psc_subst : 'Auu____6714 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____6714) FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun cfg env -> (FStar_List.fold_right (fun uu____6774 subst1 -> (match (uu____6774) with
| (binder_opt, closure) -> begin
(match (((binder_opt), (closure))) with
| (FStar_Pervasives_Native.Some (b), Clos (env1, term, memo, uu____6816)) -> begin
(

let uu____6875 = b
in (match (uu____6875) with
| (bv, uu____6883) -> begin
(

let uu____6884 = (

let uu____6885 = (FStar_Syntax_Util.is_constructed_typ bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.fstar_reflection_types_binder_lid)
in (not (uu____6885)))
in (match (uu____6884) with
| true -> begin
subst1
end
| uu____6888 -> begin
(

let term1 = (closure_as_term cfg env1 term)
in (

let uu____6890 = (unembed_binder term1)
in (match (uu____6890) with
| FStar_Pervasives_Native.None -> begin
subst1
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let b1 = (

let uu____6897 = (

let uu___219_6898 = bv
in (

let uu____6899 = (FStar_Syntax_Subst.subst subst1 (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___219_6898.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___219_6898.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6899}))
in (FStar_Syntax_Syntax.freshen_bv uu____6897))
in (

let b_for_x = (

let uu____6903 = (

let uu____6910 = (FStar_Syntax_Syntax.bv_to_name b1)
in (((FStar_Pervasives_Native.fst x)), (uu____6910)))
in FStar_Syntax_Syntax.NT (uu____6903))
in (

let subst2 = (FStar_List.filter (fun uu___184_6919 -> (match (uu___184_6919) with
| FStar_Syntax_Syntax.NT (uu____6920, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (b'); FStar_Syntax_Syntax.pos = uu____6922; FStar_Syntax_Syntax.vars = uu____6923}) -> begin
(not ((FStar_Ident.ident_equals b1.FStar_Syntax_Syntax.ppname b'.FStar_Syntax_Syntax.ppname)))
end
| uu____6928 -> begin
true
end)) subst1)
in (b_for_x)::subst2)))
end)))
end))
end))
end
| uu____6929 -> begin
subst1
end)
end)) env []))


let reduce_primops : 'Auu____6952 'Auu____6953 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____6953) FStar_Pervasives_Native.option * closure) Prims.list  ->  'Auu____6952  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 tm -> (

let uu____6994 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops cfg.steps))
in (match (uu____6994) with
| true -> begin
tm
end
| uu____6995 -> begin
(

let uu____6996 = (FStar_Syntax_Util.head_and_args tm)
in (match (uu____6996) with
| (head1, args) -> begin
(

let uu____7033 = (

let uu____7034 = (FStar_Syntax_Util.un_uinst head1)
in uu____7034.FStar_Syntax_Syntax.n)
in (match (uu____7033) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____7038 = (FStar_List.tryFind (fun ps -> (FStar_Syntax_Syntax.fv_eq_lid fv ps.name)) cfg.primitive_steps)
in (match (uu____7038) with
| FStar_Pervasives_Native.None -> begin
tm
end
| FStar_Pervasives_Native.Some (prim_step) -> begin
(match (((FStar_List.length args) < prim_step.arity)) with
| true -> begin
((log_primops cfg (fun uu____7055 -> (

let uu____7056 = (FStar_Syntax_Print.lid_to_string prim_step.name)
in (

let uu____7057 = (FStar_Util.string_of_int (FStar_List.length args))
in (

let uu____7064 = (FStar_Util.string_of_int prim_step.arity)
in (FStar_Util.print3 "primop: found partially applied %s (%s/%s args)\n" uu____7056 uu____7057 uu____7064))))));
tm;
)
end
| uu____7065 -> begin
((log_primops cfg (fun uu____7069 -> (

let uu____7070 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: trying to reduce <%s>\n" uu____7070))));
(

let psc = {psc_range = head1.FStar_Syntax_Syntax.pos; psc_subst = (fun uu____7073 -> (match (prim_step.requires_binder_substitution) with
| true -> begin
(mk_psc_subst cfg env)
end
| uu____7074 -> begin
[]
end))}
in (

let uu____7075 = (prim_step.interpretation psc args)
in (match (uu____7075) with
| FStar_Pervasives_Native.None -> begin
((log_primops cfg (fun uu____7081 -> (

let uu____7082 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: <%s> did not reduce\n" uu____7082))));
tm;
)
end
| FStar_Pervasives_Native.Some (reduced) -> begin
((log_primops cfg (fun uu____7088 -> (

let uu____7089 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____7090 = (FStar_Syntax_Print.term_to_string reduced)
in (FStar_Util.print2 "primop: <%s> reduced to <%s>\n" uu____7089 uu____7090)))));
reduced;
)
end)));
)
end)
end))
end
| uu____7091 -> begin
tm
end))
end))
end)))


let reduce_equality : 'Auu____7102 'Auu____7103 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____7103) FStar_Pervasives_Native.option * closure) Prims.list  ->  'Auu____7102  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (reduce_primops (

let uu___220_7141 = cfg
in {steps = (Primops)::[]; tcenv = uu___220_7141.tcenv; delta_level = uu___220_7141.delta_level; primitive_steps = equality_ops}) tm))


let maybe_simplify : 'Auu____7154 'Auu____7155 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____7155) FStar_Pervasives_Native.option * closure) Prims.list  ->  'Auu____7154  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 tm -> (

let tm1 = (reduce_primops cfg env stack1 tm)
in (

let uu____7197 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify cfg.steps))
in (match (uu____7197) with
| true -> begin
tm1
end
| uu____7198 -> begin
(

let w = (fun t -> (

let uu___221_7209 = t
in {FStar_Syntax_Syntax.n = uu___221_7209.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = tm1.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___221_7209.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_Pervasives_Native.Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid) -> begin
FStar_Pervasives_Native.Some (false)
end
| uu____7226 -> begin
FStar_Pervasives_Native.None
end))
in (

let simplify1 = (fun arg -> (((simp_t (FStar_Pervasives_Native.fst arg))), (arg)))
in (match (tm1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7266; FStar_Syntax_Syntax.vars = uu____7267}, uu____7268); FStar_Syntax_Syntax.pos = uu____7269; FStar_Syntax_Syntax.vars = uu____7270}, args) -> begin
(

let uu____7296 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____7296) with
| true -> begin
(

let uu____7297 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____7297) with
| ((FStar_Pervasives_Native.Some (true), uu____7352))::((uu____7353, (arg, uu____7355)))::[] -> begin
arg
end
| ((uu____7420, (arg, uu____7422)))::((FStar_Pervasives_Native.Some (true), uu____7423))::[] -> begin
arg
end
| ((FStar_Pervasives_Native.Some (false), uu____7488))::(uu____7489)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____7552)::((FStar_Pervasives_Native.Some (false), uu____7553))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____7616 -> begin
tm1
end))
end
| uu____7631 -> begin
(

let uu____7632 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____7632) with
| true -> begin
(

let uu____7633 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____7633) with
| ((FStar_Pervasives_Native.Some (true), uu____7688))::(uu____7689)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____7752)::((FStar_Pervasives_Native.Some (true), uu____7753))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____7816))::((uu____7817, (arg, uu____7819)))::[] -> begin
arg
end
| ((uu____7884, (arg, uu____7886)))::((FStar_Pervasives_Native.Some (false), uu____7887))::[] -> begin
arg
end
| uu____7952 -> begin
tm1
end))
end
| uu____7967 -> begin
(

let uu____7968 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____7968) with
| true -> begin
(

let uu____7969 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____7969) with
| (uu____8024)::((FStar_Pervasives_Native.Some (true), uu____8025))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____8088))::(uu____8089)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____8152))::((uu____8153, (arg, uu____8155)))::[] -> begin
arg
end
| ((uu____8220, (p, uu____8222)))::((uu____8223, (q, uu____8225)))::[] -> begin
(

let uu____8290 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____8290) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____8291 -> begin
tm1
end))
end
| uu____8292 -> begin
tm1
end))
end
| uu____8307 -> begin
(

let uu____8308 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____8308) with
| true -> begin
(

let uu____8309 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____8309) with
| ((FStar_Pervasives_Native.Some (true), uu____8364))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____8403))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____8442 -> begin
tm1
end))
end
| uu____8457 -> begin
(

let uu____8458 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____8458) with
| true -> begin
(match (args) with
| ((t, uu____8460))::[] -> begin
(

let uu____8477 = (

let uu____8478 = (FStar_Syntax_Subst.compress t)
in uu____8478.FStar_Syntax_Syntax.n)
in (match (uu____8477) with
| FStar_Syntax_Syntax.Tm_abs ((uu____8481)::[], body, uu____8483) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____8510 -> begin
tm1
end)
end
| uu____8513 -> begin
tm1
end))
end
| ((uu____8514, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____8515))))::((t, uu____8517))::[] -> begin
(

let uu____8556 = (

let uu____8557 = (FStar_Syntax_Subst.compress t)
in uu____8557.FStar_Syntax_Syntax.n)
in (match (uu____8556) with
| FStar_Syntax_Syntax.Tm_abs ((uu____8560)::[], body, uu____8562) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____8589 -> begin
tm1
end)
end
| uu____8592 -> begin
tm1
end))
end
| uu____8593 -> begin
tm1
end)
end
| uu____8602 -> begin
(

let uu____8603 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____8603) with
| true -> begin
(match (args) with
| ((t, uu____8605))::[] -> begin
(

let uu____8622 = (

let uu____8623 = (FStar_Syntax_Subst.compress t)
in uu____8623.FStar_Syntax_Syntax.n)
in (match (uu____8622) with
| FStar_Syntax_Syntax.Tm_abs ((uu____8626)::[], body, uu____8628) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____8655 -> begin
tm1
end)
end
| uu____8658 -> begin
tm1
end))
end
| ((uu____8659, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____8660))))::((t, uu____8662))::[] -> begin
(

let uu____8701 = (

let uu____8702 = (FStar_Syntax_Subst.compress t)
in uu____8702.FStar_Syntax_Syntax.n)
in (match (uu____8701) with
| FStar_Syntax_Syntax.Tm_abs ((uu____8705)::[], body, uu____8707) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____8734 -> begin
tm1
end)
end
| uu____8737 -> begin
tm1
end))
end
| uu____8738 -> begin
tm1
end)
end
| uu____8747 -> begin
(

let uu____8748 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
in (match (uu____8748) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____8749; FStar_Syntax_Syntax.vars = uu____8750}, uu____8751))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____8768; FStar_Syntax_Syntax.vars = uu____8769}, uu____8770))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____8787 -> begin
tm1
end)
end
| uu____8796 -> begin
(reduce_equality cfg env stack1 tm1)
end))
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8798; FStar_Syntax_Syntax.vars = uu____8799}, args) -> begin
(

let uu____8821 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____8821) with
| true -> begin
(

let uu____8822 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____8822) with
| ((FStar_Pervasives_Native.Some (true), uu____8877))::((uu____8878, (arg, uu____8880)))::[] -> begin
arg
end
| ((uu____8945, (arg, uu____8947)))::((FStar_Pervasives_Native.Some (true), uu____8948))::[] -> begin
arg
end
| ((FStar_Pervasives_Native.Some (false), uu____9013))::(uu____9014)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____9077)::((FStar_Pervasives_Native.Some (false), uu____9078))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____9141 -> begin
tm1
end))
end
| uu____9156 -> begin
(

let uu____9157 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____9157) with
| true -> begin
(

let uu____9158 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____9158) with
| ((FStar_Pervasives_Native.Some (true), uu____9213))::(uu____9214)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____9277)::((FStar_Pervasives_Native.Some (true), uu____9278))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____9341))::((uu____9342, (arg, uu____9344)))::[] -> begin
arg
end
| ((uu____9409, (arg, uu____9411)))::((FStar_Pervasives_Native.Some (false), uu____9412))::[] -> begin
arg
end
| uu____9477 -> begin
tm1
end))
end
| uu____9492 -> begin
(

let uu____9493 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____9493) with
| true -> begin
(

let uu____9494 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____9494) with
| (uu____9549)::((FStar_Pervasives_Native.Some (true), uu____9550))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____9613))::(uu____9614)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____9677))::((uu____9678, (arg, uu____9680)))::[] -> begin
arg
end
| ((uu____9745, (p, uu____9747)))::((uu____9748, (q, uu____9750)))::[] -> begin
(

let uu____9815 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____9815) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____9816 -> begin
tm1
end))
end
| uu____9817 -> begin
tm1
end))
end
| uu____9832 -> begin
(

let uu____9833 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____9833) with
| true -> begin
(

let uu____9834 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____9834) with
| ((FStar_Pervasives_Native.Some (true), uu____9889))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____9928))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____9967 -> begin
tm1
end))
end
| uu____9982 -> begin
(

let uu____9983 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____9983) with
| true -> begin
(match (args) with
| ((t, uu____9985))::[] -> begin
(

let uu____10002 = (

let uu____10003 = (FStar_Syntax_Subst.compress t)
in uu____10003.FStar_Syntax_Syntax.n)
in (match (uu____10002) with
| FStar_Syntax_Syntax.Tm_abs ((uu____10006)::[], body, uu____10008) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____10035 -> begin
tm1
end)
end
| uu____10038 -> begin
tm1
end))
end
| ((uu____10039, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10040))))::((t, uu____10042))::[] -> begin
(

let uu____10081 = (

let uu____10082 = (FStar_Syntax_Subst.compress t)
in uu____10082.FStar_Syntax_Syntax.n)
in (match (uu____10081) with
| FStar_Syntax_Syntax.Tm_abs ((uu____10085)::[], body, uu____10087) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____10114 -> begin
tm1
end)
end
| uu____10117 -> begin
tm1
end))
end
| uu____10118 -> begin
tm1
end)
end
| uu____10127 -> begin
(

let uu____10128 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____10128) with
| true -> begin
(match (args) with
| ((t, uu____10130))::[] -> begin
(

let uu____10147 = (

let uu____10148 = (FStar_Syntax_Subst.compress t)
in uu____10148.FStar_Syntax_Syntax.n)
in (match (uu____10147) with
| FStar_Syntax_Syntax.Tm_abs ((uu____10151)::[], body, uu____10153) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____10180 -> begin
tm1
end)
end
| uu____10183 -> begin
tm1
end))
end
| ((uu____10184, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10185))))::((t, uu____10187))::[] -> begin
(

let uu____10226 = (

let uu____10227 = (FStar_Syntax_Subst.compress t)
in uu____10227.FStar_Syntax_Syntax.n)
in (match (uu____10226) with
| FStar_Syntax_Syntax.Tm_abs ((uu____10230)::[], body, uu____10232) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____10259 -> begin
tm1
end)
end
| uu____10262 -> begin
tm1
end))
end
| uu____10263 -> begin
tm1
end)
end
| uu____10272 -> begin
(

let uu____10273 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
in (match (uu____10273) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____10274; FStar_Syntax_Syntax.vars = uu____10275}, uu____10276))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____10293; FStar_Syntax_Syntax.vars = uu____10294}, uu____10295))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____10312 -> begin
tm1
end)
end
| uu____10321 -> begin
(reduce_equality cfg env stack1 tm1)
end))
end))
end))
end))
end))
end))
end))
end
| uu____10322 -> begin
tm1
end))))
end))))


let is_norm_request : 'Auu____10329 . FStar_Syntax_Syntax.term  ->  'Auu____10329 Prims.list  ->  Prims.bool = (fun hd1 args -> (

let uu____10342 = (

let uu____10349 = (

let uu____10350 = (FStar_Syntax_Util.un_uinst hd1)
in uu____10350.FStar_Syntax_Syntax.n)
in ((uu____10349), (args)))
in (match (uu____10342) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____10356)::(uu____10357)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____10361)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (steps)::(uu____10366)::(uu____10367)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm)
end
| uu____10370 -> begin
false
end)))


let tr_norm_step : FStar_Syntax_Embeddings.norm_step  ->  step Prims.list = (fun uu___185_10382 -> (match (uu___185_10382) with
| FStar_Syntax_Embeddings.Zeta -> begin
(Zeta)::[]
end
| FStar_Syntax_Embeddings.Iota -> begin
(Iota)::[]
end
| FStar_Syntax_Embeddings.Delta -> begin
(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]
end
| FStar_Syntax_Embeddings.Simpl -> begin
(Simplify)::[]
end
| FStar_Syntax_Embeddings.Weak -> begin
(Weak)::[]
end
| FStar_Syntax_Embeddings.HNF -> begin
(HNF)::[]
end
| FStar_Syntax_Embeddings.Primops -> begin
(Primops)::[]
end
| FStar_Syntax_Embeddings.UnfoldOnly (names1) -> begin
(

let uu____10388 = (

let uu____10391 = (

let uu____10392 = (FStar_List.map FStar_Ident.lid_of_str names1)
in UnfoldOnly (uu____10392))
in (uu____10391)::[])
in (UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::uu____10388)
end))


let tr_norm_steps : FStar_Syntax_Embeddings.norm_step Prims.list  ->  step Prims.list = (fun s -> (FStar_List.concatMap tr_norm_step s))


let get_norm_request : 'Auu____10411 . (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term * 'Auu____10411) Prims.list  ->  (step Prims.list * FStar_Syntax_Syntax.term) = (fun full_norm args -> (

let parse_steps = (fun s -> (

let uu____10449 = (

let uu____10452 = (

let uu____10457 = (FStar_Syntax_Embeddings.unembed_list FStar_Syntax_Embeddings.unembed_norm_step)
in (uu____10457 s))
in (FStar_All.pipe_right uu____10452 FStar_Util.must))
in (FStar_All.pipe_right uu____10449 tr_norm_steps)))
in (match (args) with
| (uu____10482)::((tm, uu____10484))::[] -> begin
(

let s = (Beta)::(Zeta)::(Iota)::(Primops)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Reify)::[]
in ((s), (tm)))
end
| ((tm, uu____10507))::[] -> begin
(

let s = (Beta)::(Zeta)::(Iota)::(Primops)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Reify)::[]
in ((s), (tm)))
end
| ((steps, uu____10522))::(uu____10523)::((tm, uu____10525))::[] -> begin
(

let add_exclude = (fun s z -> (match ((not ((FStar_List.contains z s)))) with
| true -> begin
(Exclude (z))::s
end
| uu____10561 -> begin
s
end))
in (

let s = (

let uu____10565 = (

let uu____10568 = (full_norm steps)
in (parse_steps uu____10568))
in (Beta)::uu____10565)
in (

let s1 = (add_exclude s Zeta)
in (

let s2 = (add_exclude s1 Iota)
in ((s2), (tm))))))
end
| uu____10577 -> begin
(failwith "Impossible")
end)))


let is_reify_head : stack_elt Prims.list  ->  Prims.bool = (fun uu___186_10595 -> (match (uu___186_10595) with
| (App (uu____10598, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____10599; FStar_Syntax_Syntax.vars = uu____10600}, uu____10601, uu____10602))::uu____10603 -> begin
true
end
| uu____10610 -> begin
false
end))


let firstn : 'Auu____10619 . Prims.int  ->  'Auu____10619 Prims.list  ->  ('Auu____10619 Prims.list * 'Auu____10619 Prims.list) = (fun k l -> (match (((FStar_List.length l) < k)) with
| true -> begin
((l), ([]))
end
| uu____10644 -> begin
(FStar_Util.first_N k l)
end))


let should_reify : cfg  ->  stack_elt Prims.list  ->  Prims.bool = (fun cfg stack1 -> (match (stack1) with
| (App (uu____10657, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____10658; FStar_Syntax_Syntax.vars = uu____10659}, uu____10660, uu____10661))::uu____10662 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____10669 -> begin
false
end))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in ((log cfg (fun uu____10785 -> (

let uu____10786 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____10787 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10788 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____10795 = (

let uu____10796 = (

let uu____10799 = (firstn (Prims.parse_int "4") stack1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10799))
in (stack_to_string uu____10796))
in (FStar_Util.print4 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n" uu____10786 uu____10787 uu____10788 uu____10795)))))));
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____10822) -> begin
(failwith "Impossible: got a delayed substitution")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____10847) when (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars)) -> begin
(

let uu____10864 = (

let uu____10865 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____10866 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s) CheckNoUvars: Unexpected unification variable remains: %s" uu____10865 uu____10866)))
in (failwith uu____10864))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____10867) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_constant (uu____10884) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____10885) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10886; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = uu____10887}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10890; FStar_Syntax_Syntax.fv_delta = uu____10891; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10892; FStar_Syntax_Syntax.fv_delta = uu____10893; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____10894))}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____10902 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_TypeChecker_Env.is_action cfg.tcenv uu____10902)) -> begin
(

let b = (should_reify cfg stack1)
in ((log cfg (fun uu____10908 -> (

let uu____10909 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10910 = (FStar_Util.string_of_bool b)
in (FStar_Util.print2 ">>> For DM4F action %s, should_reify = %s\n" uu____10909 uu____10910)))));
(match (b) with
| true -> begin
(

let uu____10911 = (FStar_List.tl stack1)
in (do_unfold_fv cfg env uu____10911 t1 fv))
end
| uu____10914 -> begin
(rebuild cfg env stack1 t1)
end);
))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when (((FStar_Syntax_Util.is_fstar_tactics_embed hd1) || ((FStar_Syntax_Util.is_fstar_tactics_quote hd1) && (FStar_List.contains NoDeltaSteps cfg.steps))) || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)) -> begin
(

let args1 = (closures_as_args_delayed cfg env args)
in (

let hd2 = (closure_as_term cfg env hd1)
in (

let t2 = (

let uu___222_10950 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd2), (args1))); FStar_Syntax_Syntax.pos = uu___222_10950.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___222_10950.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack1 t2))))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when (((

let uu____10983 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoFullNorm))
in (not (uu____10983))) && (is_norm_request hd1 args)) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid)))) -> begin
(

let cfg' = (

let uu___223_10991 = cfg
in (

let uu____10992 = (FStar_List.filter (fun uu___187_10995 -> (match (uu___187_10995) with
| UnfoldOnly (uu____10996) -> begin
false
end
| NoDeltaSteps -> begin
false
end
| uu____10999 -> begin
true
end)) cfg.steps)
in {steps = uu____10992; tcenv = uu___223_10991.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]; primitive_steps = uu___223_10991.primitive_steps}))
in (

let uu____11000 = (get_norm_request (norm cfg' env []) args)
in (match (uu____11000) with
| (s, tm) -> begin
(

let delta_level = (

let uu____11016 = (FStar_All.pipe_right s (FStar_Util.for_some (fun uu___188_11021 -> (match (uu___188_11021) with
| UnfoldUntil (uu____11022) -> begin
true
end
| UnfoldOnly (uu____11023) -> begin
true
end
| uu____11026 -> begin
false
end))))
in (match (uu____11016) with
| true -> begin
(FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]
end
| uu____11029 -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end))
in (

let cfg'1 = (

let uu___224_11031 = cfg
in {steps = s; tcenv = uu___224_11031.tcenv; delta_level = delta_level; primitive_steps = uu___224_11031.primitive_steps})
in (

let stack' = (

let tail1 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let uu____11042 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms")))
in (match (uu____11042) with
| true -> begin
(

let uu____11045 = (

let uu____11046 = (

let uu____11051 = (FStar_Util.now ())
in ((t1), (uu____11051)))
in Debug (uu____11046))
in (uu____11045)::tail1)
end
| uu____11052 -> begin
tail1
end)))
in (norm cfg'1 env stack' tm))))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____11053; FStar_Syntax_Syntax.vars = uu____11054}, (a1)::(a2)::rest) -> begin
(

let uu____11102 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____11102) with
| (hd1, uu____11118) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), ((a1)::[])))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (norm cfg env stack1 t2)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____11183)); FStar_Syntax_Syntax.pos = uu____11184; FStar_Syntax_Syntax.vars = uu____11185}, (a)::[]) when ((FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) && (is_reify_head stack1)) -> begin
(

let uu____11217 = (FStar_List.tl stack1)
in (norm cfg env uu____11217 (FStar_Pervasives_Native.fst a)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____11220; FStar_Syntax_Syntax.vars = uu____11221}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let uu____11253 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____11253) with
| (reify_head, uu____11269) -> begin
(

let a1 = (

let uu____11291 = (FStar_All.pipe_left FStar_Syntax_Util.unascribe (FStar_Pervasives_Native.fst a))
in (FStar_Syntax_Subst.compress uu____11291))
in (match (a1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____11294)); FStar_Syntax_Syntax.pos = uu____11295; FStar_Syntax_Syntax.vars = uu____11296}, (a2)::[]) -> begin
(norm cfg env stack1 (FStar_Pervasives_Native.fst a2))
end
| uu____11330 -> begin
(

let stack2 = (App (((env), (reify_head), (FStar_Pervasives_Native.None), (t1.FStar_Syntax_Syntax.pos))))::stack1
in (norm cfg env stack2 a1))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u1 = (norm_universe cfg env u)
in (

let uu____11340 = (mk (FStar_Syntax_Syntax.Tm_type (u1)) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 uu____11340)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let uu____11347 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____11347) with
| true -> begin
(norm cfg env stack1 t')
end
| uu____11348 -> begin
(

let us1 = (

let uu____11350 = (

let uu____11357 = (FStar_List.map (norm_universe cfg env) us)
in ((uu____11357), (t1.FStar_Syntax_Syntax.pos)))
in UnivArgs (uu____11350))
in (

let stack2 = (us1)::stack1
in (norm cfg env stack2 t')))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun uu___189_11370 -> (match (uu___189_11370) with
| FStar_TypeChecker_Env.UnfoldTac -> begin
false
end
| FStar_TypeChecker_Env.NoDelta -> begin
false
end
| FStar_TypeChecker_Env.Inlining -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| FStar_TypeChecker_Env.Unfold (l) -> begin
(FStar_TypeChecker_Common.delta_depth_greater_than f.FStar_Syntax_Syntax.fv_delta l)
end))))
in (

let should_delta1 = (

let uu____11373 = ((FStar_List.mem FStar_TypeChecker_Env.UnfoldTac cfg.delta_level) && (((((((((FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.and_lid) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.imp_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.forall_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.exists_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.eq2_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.true_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.false_lid)))
in (match (uu____11373) with
| true -> begin
false
end
| uu____11374 -> begin
(

let uu____11375 = (FStar_All.pipe_right cfg.steps (FStar_List.tryFind (fun uu___190_11382 -> (match (uu___190_11382) with
| UnfoldOnly (uu____11383) -> begin
true
end
| uu____11386 -> begin
false
end))))
in (match (uu____11375) with
| FStar_Pervasives_Native.Some (UnfoldOnly (lids)) -> begin
(should_delta && (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid f) lids))
end
| uu____11390 -> begin
should_delta
end))
end))
in ((log cfg (fun uu____11398 -> (

let uu____11399 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____11400 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____11401 = (FStar_Util.string_of_bool should_delta1)
in (FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n" uu____11399 uu____11400 uu____11401))))));
(match ((not (should_delta1))) with
| true -> begin
(rebuild cfg env stack1 t1)
end
| uu____11402 -> begin
(do_unfold_fv cfg env stack1 t1 f)
end);
)))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____11404 = (lookup_bvar env x)
in (match (uu____11404) with
| Univ (uu____11407) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env1, t0, r, fix) -> begin
(match (((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps))))) with
| true -> begin
(

let uu____11456 = (FStar_ST.op_Bang r)
in (match (uu____11456) with
| FStar_Pervasives_Native.Some (env2, t') -> begin
((log cfg (fun uu____11593 -> (

let uu____11594 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____11595 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" uu____11594 uu____11595)))));
(

let uu____11596 = (

let uu____11597 = (FStar_Syntax_Subst.compress t')
in uu____11597.FStar_Syntax_Syntax.n)
in (match (uu____11596) with
| FStar_Syntax_Syntax.Tm_abs (uu____11600) -> begin
(norm cfg env2 stack1 t')
end
| uu____11617 -> begin
(rebuild cfg env2 stack1 t')
end));
)
end
| FStar_Pervasives_Native.None -> begin
(norm cfg env1 ((MemoLazy (r))::stack1) t0)
end))
end
| uu____11651 -> begin
(norm cfg env1 stack1 t0)
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack1) with
| (UnivArgs (uu____11675))::uu____11676 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (uu____11685))::uu____11686 -> begin
(failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, uu____11696, uu____11697))::stack_rest -> begin
(match (c) with
| Univ (uu____11701) -> begin
(norm cfg ((((FStar_Pervasives_Native.None), (c)))::env) stack_rest t1)
end
| uu____11710 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (b)::[] -> begin
((log cfg (fun uu____11731 -> (

let uu____11732 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____11732))));
(norm cfg ((((FStar_Pervasives_Native.Some (b)), (c)))::env) stack_rest body);
)
end
| (b)::tl1 -> begin
((log cfg (fun uu____11772 -> (

let uu____11773 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____11773))));
(

let body1 = (mk (FStar_Syntax_Syntax.Tm_abs (((tl1), (body), (lopt)))) t1.FStar_Syntax_Syntax.pos)
in (norm cfg ((((FStar_Pervasives_Native.Some (b)), (c)))::env) stack_rest body1));
)
end)
end)
end
| (Steps (s, ps, dl))::stack2 -> begin
(norm (

let uu___225_11823 = cfg
in {steps = s; tcenv = uu___225_11823.tcenv; delta_level = dl; primitive_steps = ps}) env stack2 t1)
end
| (MemoLazy (r))::stack2 -> begin
((set_memo r ((env), (t1)));
(log cfg (fun uu____11856 -> (

let uu____11857 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____11857))));
(norm cfg env stack2 t1);
)
end
| (Debug (uu____11858))::uu____11859 -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(

let uu____11866 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____11866))
end
| uu____11867 -> begin
(

let uu____11868 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11868) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11910 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____11938 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____11938) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11948 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11948))))
end
| uu____11949 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___226_11953 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___226_11953.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___226_11953.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11954 -> begin
lopt
end)
in ((log cfg (fun uu____11960 -> (

let uu____11961 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11961))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (only_strong_steps cfg)
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Meta (uu____11984))::uu____11985 -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(

let uu____11992 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____11992))
end
| uu____11993 -> begin
(

let uu____11994 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11994) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____12036 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____12064 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____12064) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____12074 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____12074))))
end
| uu____12075 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___226_12079 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___226_12079.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___226_12079.FStar_Syntax_Syntax.residual_flags})))
end
| uu____12080 -> begin
lopt
end)
in ((log cfg (fun uu____12086 -> (

let uu____12087 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____12087))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (only_strong_steps cfg)
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Let (uu____12110))::uu____12111 -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(

let uu____12122 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12122))
end
| uu____12123 -> begin
(

let uu____12124 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____12124) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____12166 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____12194 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____12194) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____12204 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____12204))))
end
| uu____12205 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___226_12209 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___226_12209.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___226_12209.FStar_Syntax_Syntax.residual_flags})))
end
| uu____12210 -> begin
lopt
end)
in ((log cfg (fun uu____12216 -> (

let uu____12217 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____12217))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (only_strong_steps cfg)
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (App (uu____12240))::uu____12241 -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(

let uu____12252 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12252))
end
| uu____12253 -> begin
(

let uu____12254 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____12254) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____12296 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____12324 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____12324) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____12334 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____12334))))
end
| uu____12335 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___226_12339 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___226_12339.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___226_12339.FStar_Syntax_Syntax.residual_flags})))
end
| uu____12340 -> begin
lopt
end)
in ((log cfg (fun uu____12346 -> (

let uu____12347 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____12347))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (only_strong_steps cfg)
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Abs (uu____12370))::uu____12371 -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(

let uu____12386 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12386))
end
| uu____12387 -> begin
(

let uu____12388 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____12388) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____12430 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____12458 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____12458) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____12468 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____12468))))
end
| uu____12469 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___226_12473 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___226_12473.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___226_12473.FStar_Syntax_Syntax.residual_flags})))
end
| uu____12474 -> begin
lopt
end)
in ((log cfg (fun uu____12480 -> (

let uu____12481 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____12481))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (only_strong_steps cfg)
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| [] -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(

let uu____12504 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12504))
end
| uu____12505 -> begin
(

let uu____12506 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____12506) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____12548 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____12576 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____12576) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____12586 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____12586))))
end
| uu____12587 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___226_12591 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___226_12591.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___226_12591.FStar_Syntax_Syntax.residual_flags})))
end
| uu____12592 -> begin
lopt
end)
in ((log cfg (fun uu____12598 -> (

let uu____12599 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____12599))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (only_strong_steps cfg)
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack2 = (FStar_All.pipe_right stack1 (FStar_List.fold_right (fun uu____12660 stack2 -> (match (uu____12660) with
| (a, aq) -> begin
(

let uu____12672 = (

let uu____12673 = (

let uu____12680 = (

let uu____12681 = (

let uu____12712 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____12712), (false)))
in Clos (uu____12681))
in ((uu____12680), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____12673))
in (uu____12672)::stack2)
end)) args))
in ((log cfg (fun uu____12788 -> (

let uu____12789 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____12789))));
(norm cfg env stack2 head1);
))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(match (((env), (stack1))) with
| ([], []) -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let t2 = (mk (FStar_Syntax_Syntax.Tm_refine ((((

let uu___227_12825 = x
in {FStar_Syntax_Syntax.ppname = uu___227_12825.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___227_12825.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 t2)))
end
| uu____12826 -> begin
(

let uu____12831 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12831))
end)
end
| uu____12832 -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let uu____12834 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____12834) with
| (closing, f1) -> begin
(

let f2 = (norm cfg ((dummy)::env) [] f1)
in (

let t2 = (

let uu____12865 = (

let uu____12866 = (

let uu____12873 = (FStar_Syntax_Subst.close closing f2)
in (((

let uu___228_12875 = x
in {FStar_Syntax_Syntax.ppname = uu___228_12875.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___228_12875.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (uu____12873)))
in FStar_Syntax_Syntax.Tm_refine (uu____12866))
in (mk uu____12865 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack1 t2)))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(

let uu____12894 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12894))
end
| uu____12895 -> begin
(

let uu____12896 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____12896) with
| (bs1, c1) -> begin
(

let c2 = (

let uu____12904 = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____12928 -> (dummy)::env1) env))
in (norm_comp cfg uu____12904 c1))
in (

let t2 = (

let uu____12950 = (norm_binders cfg env bs1)
in (FStar_Syntax_Util.arrow uu____12950 c2))
in (rebuild cfg env stack1 t2)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) -> begin
(match (stack1) with
| (Match (uu____13009))::uu____13010 -> begin
((log cfg (fun uu____13021 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack1 t11);
)
end
| (Arg (uu____13022))::uu____13023 -> begin
((log cfg (fun uu____13034 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack1 t11);
)
end
| (App (uu____13035, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____13036; FStar_Syntax_Syntax.vars = uu____13037}, uu____13038, uu____13039))::uu____13040 -> begin
((log cfg (fun uu____13049 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack1 t11);
)
end
| (MemoLazy (uu____13050))::uu____13051 -> begin
((log cfg (fun uu____13062 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack1 t11);
)
end
| uu____13063 -> begin
((log cfg (fun uu____13066 -> (FStar_Util.print_string "+++ Keeping ascription \n")));
(

let t12 = (norm cfg env [] t11)
in ((log cfg (fun uu____13070 -> (FStar_Util.print_string "+++ Normalizing ascription \n")));
(

let tc1 = (match (tc) with
| FStar_Util.Inl (t2) -> begin
(

let uu____13087 = (norm cfg env [] t2)
in FStar_Util.Inl (uu____13087))
end
| FStar_Util.Inr (c) -> begin
(

let uu____13095 = (norm_comp cfg env c)
in FStar_Util.Inr (uu____13095))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (norm cfg env []))
in (

let uu____13101 = (

let uu____13102 = (

let uu____13103 = (

let uu____13130 = (FStar_Syntax_Util.unascribe t12)
in ((uu____13130), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____13103))
in (mk uu____13102 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack1 uu____13101))));
));
)
end)
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let stack2 = (Match (((env), (branches), (t1.FStar_Syntax_Syntax.pos))))::stack1
in (norm cfg env stack2 head1))
end
| FStar_Syntax_Syntax.Tm_let ((uu____13206, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____13207); FStar_Syntax_Syntax.lbunivs = uu____13208; FStar_Syntax_Syntax.lbtyp = uu____13209; FStar_Syntax_Syntax.lbeff = uu____13210; FStar_Syntax_Syntax.lbdef = uu____13211})::uu____13212), uu____13213) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n1 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in (

let uu____13249 = ((

let uu____13252 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps))
in (not (uu____13252))) && ((FStar_Syntax_Util.is_pure_effect n1) || ((FStar_Syntax_Util.is_ghost_effect n1) && (

let uu____13254 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (not (uu____13254))))))
in (match (uu____13249) with
| true -> begin
(

let binder = (

let uu____13256 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____13256))
in (

let env1 = (

let uu____13266 = (

let uu____13273 = (

let uu____13274 = (

let uu____13305 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (uu____13305), (false)))
in Clos (uu____13274))
in ((FStar_Pervasives_Native.Some (binder)), (uu____13273)))
in (uu____13266)::env)
in ((log cfg (fun uu____13390 -> (FStar_Util.print_string "+++ Reducing Tm_let\n")));
(norm cfg env1 stack1 body);
)))
end
| uu____13391 -> begin
(

let uu____13392 = (

let uu____13397 = (

let uu____13398 = (

let uu____13399 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right uu____13399 FStar_Syntax_Syntax.mk_binder))
in (uu____13398)::[])
in (FStar_Syntax_Subst.open_term uu____13397 body))
in (match (uu____13392) with
| (bs, body1) -> begin
((log cfg (fun uu____13408 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- type\n")));
(

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let x = (

let uu____13416 = (FStar_List.hd bs)
in (FStar_Pervasives_Native.fst uu____13416))
in FStar_Util.Inl ((

let uu___229_13426 = x
in {FStar_Syntax_Syntax.ppname = uu___229_13426.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___229_13426.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
in ((log cfg (fun uu____13429 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- definiens\n")));
(

let lb1 = (

let uu___230_13431 = lb
in (

let uu____13432 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___230_13431.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___230_13431.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____13432}))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env1 uu____13467 -> (dummy)::env1) env))
in (

let cfg1 = (only_strong_steps cfg)
in ((log cfg1 (fun uu____13489 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- body\n")));
(norm cfg1 env' ((Let (((env), (bs), (lb1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1);
))));
)));
)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), body) when ((FStar_List.contains CompressUvars cfg.steps) || ((FStar_List.contains (Exclude (Zeta)) cfg.steps) && (FStar_List.contains PureSubtermsWithinComputations cfg.steps))) -> begin
(

let uu____13506 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____13506) with
| (lbs1, body1) -> begin
(

let lbs2 = (FStar_List.map (fun lb -> (

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let uu____13542 = (

let uu___231_13543 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___231_13543.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___231_13543.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})
in FStar_Util.Inl (uu____13542))
in (

let uu____13544 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____13544) with
| (xs, def_body, lopt) -> begin
(

let xs1 = (norm_binders cfg env xs)
in (

let env1 = (

let uu____13570 = (FStar_List.map (fun uu____13586 -> dummy) lbs1)
in (

let uu____13587 = (

let uu____13596 = (FStar_List.map (fun uu____13616 -> dummy) xs1)
in (FStar_List.append uu____13596 env))
in (FStar_List.append uu____13570 uu____13587)))
in (

let def_body1 = (norm cfg env1 [] def_body)
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____13640 = (

let uu___232_13641 = rc
in (

let uu____13642 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env1 []))
in {FStar_Syntax_Syntax.residual_effect = uu___232_13641.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____13642; FStar_Syntax_Syntax.residual_flags = uu___232_13641.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____13640))
end
| uu____13649 -> begin
lopt
end)
in (

let def = (FStar_Syntax_Util.abs xs1 def_body1 lopt1)
in (

let uu___233_13653 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___233_13653.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___233_13653.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def}))))))
end))))) lbs1)
in (

let env' = (

let uu____13663 = (FStar_List.map (fun uu____13679 -> dummy) lbs2)
in (FStar_List.append uu____13663 env))
in (

let body2 = (norm cfg env' [] body1)
in (

let uu____13687 = (FStar_Syntax_Subst.close_let_rec lbs2 body2)
in (match (uu____13687) with
| (lbs3, body3) -> begin
(

let t2 = (

let uu___234_13703 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (body3))); FStar_Syntax_Syntax.pos = uu___234_13703.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___234_13703.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack1 t2))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(

let uu____13730 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____13730))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let uu____13749 = (FStar_List.fold_right (fun lb uu____13825 -> (match (uu____13825) with
| (rec_env, memos, i) -> begin
(

let bv = (

let uu___235_13946 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___235_13946.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___235_13946.FStar_Syntax_Syntax.sort})
in (

let f_i = (FStar_Syntax_Syntax.bv_to_tm bv)
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t1.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let rec_env1 = (((FStar_Pervasives_Native.None), (Clos (((env), (fix_f_i), (memo), (true))))))::rec_env
in ((rec_env1), ((memo)::memos), ((i + (Prims.parse_int "1")))))))))
end)) (FStar_Pervasives_Native.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (uu____13749) with
| (rec_env, memos, uu____14143) -> begin
(

let uu____14196 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (FStar_Pervasives_Native.Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (FStar_Pervasives_Native.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env1 -> (

let uu____14727 = (

let uu____14734 = (

let uu____14735 = (

let uu____14766 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (uu____14766), (false)))
in Clos (uu____14735))
in ((FStar_Pervasives_Native.None), (uu____14734)))
in (uu____14727)::env1)) (FStar_Pervasives_Native.snd lbs) env)
in (norm cfg body_env stack1 body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head1, m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m1, t2) -> begin
(

let uu____14871 = (

let uu____14872 = (should_reify cfg stack1)
in (not (uu____14872)))
in (match (uu____14871) with
| true -> begin
(

let t3 = (norm cfg env [] t2)
in (

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu____14882 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____14882) with
| true -> begin
(

let uu___236_14883 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::(NoDeltaSteps)::[]; tcenv = uu___236_14883.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___236_14883.primitive_steps})
end
| uu____14884 -> begin
(

let uu___237_14885 = cfg
in {steps = (FStar_List.append ((Exclude (Zeta))::[]) cfg.steps); tcenv = uu___237_14885.tcenv; delta_level = uu___237_14885.delta_level; primitive_steps = uu___237_14885.primitive_steps})
end))
in (norm cfg1 env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m1), (t3)))), (t3.FStar_Syntax_Syntax.pos))))::stack2) head1))))
end
| uu____14886 -> begin
(

let uu____14887 = (

let uu____14888 = (FStar_Syntax_Subst.compress head1)
in uu____14888.FStar_Syntax_Syntax.n)
in (match (uu____14887) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m1)
in (

let uu____14906 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____14906) with
| (uu____14907, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____14913) -> begin
(failwith "Cannot reify a top-level let binding")
end
| FStar_Util.Inl (x) -> begin
(

let is_return = (fun e -> (

let uu____14921 = (

let uu____14922 = (FStar_Syntax_Subst.compress e)
in uu____14922.FStar_Syntax_Syntax.n)
in (match (uu____14921) with
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____14928, uu____14929)) -> begin
(

let uu____14938 = (

let uu____14939 = (FStar_Syntax_Subst.compress e1)
in uu____14939.FStar_Syntax_Syntax.n)
in (match (uu____14938) with
| FStar_Syntax_Syntax.Tm_meta (e2, FStar_Syntax_Syntax.Meta_monadic_lift (uu____14945, msrc, uu____14947)) when (FStar_Syntax_Util.is_pure_effect msrc) -> begin
(

let uu____14956 = (FStar_Syntax_Subst.compress e2)
in FStar_Pervasives_Native.Some (uu____14956))
end
| uu____14957 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____14958 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____14959 = (is_return lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____14959) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let lb1 = (

let uu___238_14964 = lb
in {FStar_Syntax_Syntax.lbname = uu___238_14964.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___238_14964.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___238_14964.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = e})
in (

let uu____14965 = (FStar_List.tl stack1)
in (

let uu____14966 = (

let uu____14967 = (

let uu____14970 = (

let uu____14971 = (

let uu____14984 = (FStar_Syntax_Util.mk_reify body)
in ((((false), ((lb1)::[]))), (uu____14984)))
in FStar_Syntax_Syntax.Tm_let (uu____14971))
in (FStar_Syntax_Syntax.mk uu____14970))
in (uu____14967 FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos))
in (norm cfg env uu____14965 uu____14966))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____15000 = (

let uu____15001 = (is_return body)
in (match (uu____15001) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_bvar (y); FStar_Syntax_Syntax.pos = uu____15005; FStar_Syntax_Syntax.vars = uu____15006}) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____15011 -> begin
false
end))
in (match (uu____15000) with
| true -> begin
(norm cfg env stack1 lb.FStar_Syntax_Syntax.lbdef)
end
| uu____15014 -> begin
(

let head2 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body1 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify body)
in (

let body_rc = {FStar_Syntax_Syntax.residual_effect = m1; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t2); FStar_Syntax_Syntax.residual_flags = []}
in (

let body2 = (

let uu____15035 = (

let uu____15038 = (

let uu____15039 = (

let uu____15056 = (

let uu____15059 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____15059)::[])
in ((uu____15056), (body1), (FStar_Pervasives_Native.Some (body_rc))))
in FStar_Syntax_Syntax.Tm_abs (uu____15039))
in (FStar_Syntax_Syntax.mk uu____15038))
in (uu____15035 FStar_Pervasives_Native.None body1.FStar_Syntax_Syntax.pos))
in (

let close1 = (closure_as_term cfg env)
in (

let bind_inst = (

let uu____15075 = (

let uu____15076 = (FStar_Syntax_Subst.compress bind_repr)
in uu____15076.FStar_Syntax_Syntax.n)
in (match (uu____15075) with
| FStar_Syntax_Syntax.Tm_uinst (bind1, (uu____15082)::(uu____15083)::[]) -> begin
(

let uu____15090 = (

let uu____15093 = (

let uu____15094 = (

let uu____15101 = (

let uu____15104 = (

let uu____15105 = (close1 lb.FStar_Syntax_Syntax.lbtyp)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____15105))
in (

let uu____15106 = (

let uu____15109 = (

let uu____15110 = (close1 t2)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____15110))
in (uu____15109)::[])
in (uu____15104)::uu____15106))
in ((bind1), (uu____15101)))
in FStar_Syntax_Syntax.Tm_uinst (uu____15094))
in (FStar_Syntax_Syntax.mk uu____15093))
in (uu____15090 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
end
| uu____15118 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let reified = (

let uu____15124 = (

let uu____15127 = (

let uu____15128 = (

let uu____15143 = (

let uu____15146 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____15147 = (

let uu____15150 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____15151 = (

let uu____15154 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____15155 = (

let uu____15158 = (FStar_Syntax_Syntax.as_arg head2)
in (

let uu____15159 = (

let uu____15162 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____15163 = (

let uu____15166 = (FStar_Syntax_Syntax.as_arg body2)
in (uu____15166)::[])
in (uu____15162)::uu____15163))
in (uu____15158)::uu____15159))
in (uu____15154)::uu____15155))
in (uu____15150)::uu____15151))
in (uu____15146)::uu____15147))
in ((bind_inst), (uu____15143)))
in FStar_Syntax_Syntax.Tm_app (uu____15128))
in (FStar_Syntax_Syntax.mk uu____15127))
in (uu____15124 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (

let uu____15174 = (FStar_List.tl stack1)
in (norm cfg env uu____15174 reified)))))))))
end))
end)))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head_app, args) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m1)
in (

let uu____15198 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____15198) with
| (uu____15199, bind_repr) -> begin
(

let maybe_unfold_action = (fun head2 -> (

let maybe_extract_fv = (fun t3 -> (

let t4 = (

let uu____15234 = (

let uu____15235 = (FStar_Syntax_Subst.compress t3)
in uu____15235.FStar_Syntax_Syntax.n)
in (match (uu____15234) with
| FStar_Syntax_Syntax.Tm_uinst (t4, uu____15241) -> begin
t4
end
| uu____15246 -> begin
head2
end))
in (

let uu____15247 = (

let uu____15248 = (FStar_Syntax_Subst.compress t4)
in uu____15248.FStar_Syntax_Syntax.n)
in (match (uu____15247) with
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____15254 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____15255 = (maybe_extract_fv head2)
in (match (uu____15255) with
| FStar_Pervasives_Native.Some (x) when (

let uu____15265 = (FStar_Syntax_Syntax.lid_of_fv x)
in (FStar_TypeChecker_Env.is_action cfg.tcenv uu____15265)) -> begin
(

let head3 = (norm cfg env [] head2)
in (

let action_unfolded = (

let uu____15270 = (maybe_extract_fv head3)
in (match (uu____15270) with
| FStar_Pervasives_Native.Some (uu____15275) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____15276 -> begin
FStar_Pervasives_Native.Some (false)
end))
in ((head3), (action_unfolded))))
end
| uu____15281 -> begin
((head2), (FStar_Pervasives_Native.None))
end))))
in ((

let is_arg_impure = (fun uu____15296 -> (match (uu____15296) with
| (e, q) -> begin
(

let uu____15303 = (

let uu____15304 = (FStar_Syntax_Subst.compress e)
in uu____15304.FStar_Syntax_Syntax.n)
in (match (uu____15303) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m11, m2, t')) -> begin
(not ((FStar_Syntax_Util.is_pure_effect m11)))
end
| uu____15319 -> begin
false
end))
end))
in (

let uu____15320 = (

let uu____15321 = (

let uu____15328 = (FStar_Syntax_Syntax.as_arg head_app)
in (uu____15328)::args)
in (FStar_Util.for_some is_arg_impure uu____15321))
in (match (uu____15320) with
| true -> begin
(

let uu____15333 = (

let uu____15334 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format1 "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n" uu____15334))
in (failwith uu____15333))
end
| uu____15335 -> begin
()
end)));
(

let uu____15336 = (maybe_unfold_action head_app)
in (match (uu____15336) with
| (head_app1, found_action) -> begin
(

let mk1 = (fun tm -> (FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (

let body = (mk1 (FStar_Syntax_Syntax.Tm_app (((head_app1), (args)))))
in (

let body1 = (match (found_action) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Util.mk_reify body)
end
| FStar_Pervasives_Native.Some (false) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_monadic (((m1), (t2))))))))
end
| FStar_Pervasives_Native.Some (true) -> begin
body
end)
in (

let uu____15375 = (FStar_List.tl stack1)
in (norm cfg env uu____15375 body1)))))
end));
))
end)))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (

let uu____15389 = (closure_as_term cfg env t')
in (reify_lift cfg.tcenv e msrc mtgt uu____15389))
in (

let uu____15390 = (FStar_List.tl stack1)
in (norm cfg env uu____15390 lifted)))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____15511 -> (match (uu____15511) with
| (pat, wopt, tm) -> begin
(

let uu____15559 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____15559)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches1)))) t2.FStar_Syntax_Syntax.pos)
in (

let uu____15591 = (FStar_List.tl stack1)
in (norm cfg env uu____15591 tm))))
end
| uu____15592 -> begin
(norm cfg env stack1 head1)
end))
end))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) -> begin
(

let uu____15600 = (should_reify cfg stack1)
in (match (uu____15600) with
| true -> begin
(

let uu____15601 = (FStar_List.tl stack1)
in (

let uu____15602 = (

let uu____15603 = (closure_as_term cfg env t2)
in (reify_lift cfg.tcenv head1 m1 m' uu____15603))
in (norm cfg env uu____15601 uu____15602)))
end
| uu____15604 -> begin
(

let t3 = (norm cfg env [] t2)
in (

let uu____15606 = (((FStar_Syntax_Util.is_pure_effect m1) || (FStar_Syntax_Util.is_ghost_effect m1)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)))
in (match (uu____15606) with
| true -> begin
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___239_15615 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = uu___239_15615.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___239_15615.primitive_steps})
in (norm cfg1 env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t3)))), (head1.FStar_Syntax_Syntax.pos))))::stack2) head1)))
end
| uu____15616 -> begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t3)))), (head1.FStar_Syntax_Syntax.pos))))::stack1) head1)
end)))
end))
end
| uu____15617 -> begin
(match ((FStar_List.contains Unmeta cfg.steps)) with
| true -> begin
(norm cfg env stack1 head1)
end
| uu____15618 -> begin
(match (stack1) with
| (uu____15619)::uu____15620 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____15625) -> begin
(norm cfg env ((Meta (((m), (r))))::stack1) head1)
end
| FStar_Syntax_Syntax.Meta_alien (uu____15626) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args1 = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args1)), (t1.FStar_Syntax_Syntax.pos))))::stack1) head1))
end
| uu____15657 -> begin
(norm cfg env stack1 head1)
end)
end
| [] -> begin
(

let head2 = (norm cfg env [] head1)
in (

let m1 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let uu____15671 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (uu____15671))
end
| uu____15682 -> begin
m
end)
in (

let t2 = (mk (FStar_Syntax_Syntax.Tm_meta (((head2), (m1)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 t2))))
end)
end)
end)
end);
)))
and do_unfold_fv : cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 t0 f -> (

let r_env = (

let uu____15694 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv uu____15694))
in (

let uu____15695 = (FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____15695) with
| FStar_Pervasives_Native.None -> begin
((log cfg (fun uu____15708 -> (FStar_Util.print "Tm_fvar case 2\n" [])));
(rebuild cfg env stack1 t0);
)
end
| FStar_Pervasives_Native.Some (us, t) -> begin
((log cfg (fun uu____15719 -> (

let uu____15720 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____15721 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15720 uu____15721)))));
(

let t1 = (

let uu____15723 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))))
in (match (uu____15723) with
| true -> begin
t
end
| uu____15724 -> begin
(FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) t)
end))
in (

let n1 = (FStar_List.length us)
in (match ((n1 > (Prims.parse_int "0"))) with
| true -> begin
(match (stack1) with
| (UnivArgs (us', uu____15733))::stack2 -> begin
(

let env1 = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env1 u -> (((FStar_Pervasives_Native.None), (Univ (u))))::env1) env))
in (norm cfg env1 stack2 t1))
end
| uu____15788 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack1 t1)
end
| uu____15791 -> begin
(

let uu____15794 = (

let uu____15795 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" uu____15795))
in (failwith uu____15794))
end)
end
| uu____15796 -> begin
(norm cfg env stack1 t1)
end)));
)
end))))
and reify_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env e msrc mtgt t -> (match ((FStar_Syntax_Util.is_pure_effect msrc)) with
| true -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl env mtgt)
in (

let uu____15805 = ed.FStar_Syntax_Syntax.return_repr
in (match (uu____15805) with
| (uu____15806, return_repr) -> begin
(

let return_inst = (

let uu____15815 = (

let uu____15816 = (FStar_Syntax_Subst.compress return_repr)
in uu____15816.FStar_Syntax_Syntax.n)
in (match (uu____15815) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (uu____15822)::[]) -> begin
(

let uu____15829 = (

let uu____15832 = (

let uu____15833 = (

let uu____15840 = (

let uu____15843 = (env.FStar_TypeChecker_Env.universe_of env t)
in (uu____15843)::[])
in ((return_tm), (uu____15840)))
in FStar_Syntax_Syntax.Tm_uinst (uu____15833))
in (FStar_Syntax_Syntax.mk uu____15832))
in (uu____15829 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end
| uu____15851 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let uu____15854 = (

let uu____15857 = (

let uu____15858 = (

let uu____15873 = (

let uu____15876 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____15877 = (

let uu____15880 = (FStar_Syntax_Syntax.as_arg e)
in (uu____15880)::[])
in (uu____15876)::uu____15877))
in ((return_inst), (uu____15873)))
in FStar_Syntax_Syntax.Tm_app (uu____15858))
in (FStar_Syntax_Syntax.mk uu____15857))
in (uu____15854 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end)))
end
| uu____15888 -> begin
(

let uu____15889 = (FStar_TypeChecker_Env.monad_leq env msrc mtgt)
in (match (uu____15889) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15892 = (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" (FStar_Ident.text_of_lid msrc) (FStar_Ident.text_of_lid mtgt))
in (failwith uu____15892))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____15893; FStar_TypeChecker_Env.mtarget = uu____15894; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____15895; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(failwith "Impossible : trying to reify a non-reifiable lift (from %s to %s)")
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____15906; FStar_TypeChecker_Env.mtarget = uu____15907; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____15908; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let uu____15926 = (FStar_Syntax_Util.mk_reify e)
in (lift t FStar_Syntax_Syntax.tun uu____15926))
end))
end))
and norm_pattern_args : cfg  ->  env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun uu____15982 -> (match (uu____15982) with
| (a, imp) -> begin
(

let uu____15993 = (norm cfg env [] a)
in ((uu____15993), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp1 = (ghost_to_pure_aux cfg env comp)
in (match (comp1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu___240_16010 = comp1
in (

let uu____16013 = (

let uu____16014 = (

let uu____16023 = (norm cfg env [] t)
in (

let uu____16024 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____16023), (uu____16024))))
in FStar_Syntax_Syntax.Total (uu____16014))
in {FStar_Syntax_Syntax.n = uu____16013; FStar_Syntax_Syntax.pos = uu___240_16010.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___240_16010.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu___241_16039 = comp1
in (

let uu____16042 = (

let uu____16043 = (

let uu____16052 = (norm cfg env [] t)
in (

let uu____16053 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____16052), (uu____16053))))
in FStar_Syntax_Syntax.GTotal (uu____16043))
in {FStar_Syntax_Syntax.n = uu____16042; FStar_Syntax_Syntax.pos = uu___241_16039.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___241_16039.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____16105 -> (match (uu____16105) with
| (a, i) -> begin
(

let uu____16116 = (norm cfg env [] a)
in ((uu____16116), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___191_16127 -> (match (uu___191_16127) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____16131 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____16131))
end
| f -> begin
f
end))))
in (

let uu___242_16135 = comp1
in (

let uu____16138 = (

let uu____16139 = (

let uu___243_16140 = ct
in (

let uu____16141 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (

let uu____16142 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____16145 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = uu____16141; FStar_Syntax_Syntax.effect_name = uu___243_16140.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____16142; FStar_Syntax_Syntax.effect_args = uu____16145; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (uu____16139))
in {FStar_Syntax_Syntax.n = uu____16138; FStar_Syntax_Syntax.pos = uu___242_16135.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___242_16135.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm1 = (fun t -> (norm (

let uu___244_16163 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = uu___244_16163.tcenv; delta_level = uu___244_16163.delta_level; primitive_steps = uu___244_16163.primitive_steps}) env [] t))
in (

let non_info = (fun t -> (

let uu____16168 = (norm1 t)
in (FStar_Syntax_Util.non_informative uu____16168)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____16171) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let uu___245_16190 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.pos = uu___245_16190.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___245_16190.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____16197 = ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ))
in (match (uu____16197) with
| true -> begin
(

let ct1 = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let flags = (match ((FStar_Ident.lid_equals pure_eff FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::ct.FStar_Syntax_Syntax.flags
end
| uu____16207 -> begin
ct.FStar_Syntax_Syntax.flags
end)
in (

let uu___246_16208 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___246_16208.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = uu___246_16208.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___246_16208.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags}))
end
| FStar_Pervasives_Native.None -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c)
in (

let uu___247_16210 = ct1
in {FStar_Syntax_Syntax.comp_univs = uu___247_16210.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu___247_16210.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___247_16210.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___247_16210.FStar_Syntax_Syntax.flags}))
end)
in (

let uu___248_16211 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___248_16211.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___248_16211.FStar_Syntax_Syntax.vars}))
end
| uu____16212 -> begin
c
end)))
end
| uu____16213 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env uu____16216 -> (match (uu____16216) with
| (x, imp) -> begin
(

let uu____16219 = (

let uu___249_16220 = x
in (

let uu____16221 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___249_16220.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___249_16220.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____16221}))
in ((uu____16219), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let uu____16227 = (FStar_List.fold_left (fun uu____16245 b -> (match (uu____16245) with
| (nbs', env1) -> begin
(

let b1 = (norm_binder cfg env1 b)
in (((b1)::nbs'), ((dummy)::env1)))
end)) (([]), (env)) bs)
in (match (uu____16227) with
| (nbs, uu____16285) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags = (filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags)
in (

let uu____16301 = (

let uu___250_16302 = rc
in (

let uu____16303 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___250_16302.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____16303; FStar_Syntax_Syntax.residual_flags = uu___250_16302.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____16301)))
end
| uu____16310 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 t -> ((log cfg (fun uu____16323 -> (

let uu____16324 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____16325 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____16326 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____16333 = (

let uu____16334 = (

let uu____16337 = (firstn (Prims.parse_int "4") stack1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____16337))
in (stack_to_string uu____16334))
in (FStar_Util.print4 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n" uu____16324 uu____16325 uu____16326 uu____16333)))))));
(match (stack1) with
| [] -> begin
t
end
| (Debug (tm, time_then))::stack2 -> begin
((

let uu____16366 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms")))
in (match (uu____16366) with
| true -> begin
(

let time_now = (FStar_Util.now ())
in (

let uu____16368 = (

let uu____16369 = (

let uu____16370 = (FStar_Util.time_diff time_then time_now)
in (FStar_Pervasives_Native.snd uu____16370))
in (FStar_Util.string_of_int uu____16369))
in (

let uu____16375 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____16376 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n" uu____16368 uu____16375 uu____16376)))))
end
| uu____16377 -> begin
()
end));
(rebuild cfg env stack2 t);
)
end
| (Steps (s, ps, dl))::stack2 -> begin
(rebuild (

let uu___251_16394 = cfg
in {steps = s; tcenv = uu___251_16394.tcenv; delta_level = dl; primitive_steps = ps}) env stack2 t)
end
| (Meta (m, r))::stack2 -> begin
(

let t1 = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack2 t1))
end
| (MemoLazy (r))::stack2 -> begin
((set_memo r ((env), (t)));
(log cfg (fun uu____16435 -> (

let uu____16436 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" uu____16436))));
(rebuild cfg env stack2 t);
)
end
| (Let (env', bs, lb, r))::stack2 -> begin
(

let body = (FStar_Syntax_Subst.close bs t)
in (

let t1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) FStar_Pervasives_Native.None r)
in (rebuild cfg env' stack2 t1)))
end
| (Abs (env', bs, env'', lopt, r))::stack2 -> begin
(

let bs1 = (norm_binders cfg env' bs)
in (

let lopt1 = (norm_lcomp_opt cfg env'' lopt)
in (

let uu____16472 = (

let uu___252_16473 = (FStar_Syntax_Util.abs bs1 t lopt1)
in {FStar_Syntax_Syntax.n = uu___252_16473.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___252_16473.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack2 uu____16472))))
end
| (Arg (Univ (uu____16474), uu____16475, uu____16476))::uu____16477 -> begin
(failwith "Impossible")
end
| (Arg (Dummy, uu____16480, uu____16481))::uu____16482 -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack2 -> begin
(

let t1 = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack2 t1))
end
| (Arg (Clos (env_arg, tm, m, uu____16498), aq, r))::stack2 -> begin
((log cfg (fun uu____16551 -> (

let uu____16552 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" uu____16552))));
(match ((FStar_List.contains (Exclude (Iota)) cfg.steps)) with
| true -> begin
(match ((FStar_List.contains HNF cfg.steps)) with
| true -> begin
(

let arg = (closure_as_term cfg env_arg tm)
in (

let t1 = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack2 t1)))
end
| uu____16557 -> begin
(

let stack3 = (App (((env), (t), (aq), (r))))::stack2
in (norm cfg env_arg stack3 tm))
end)
end
| uu____16561 -> begin
(

let uu____16562 = (FStar_ST.op_Bang m)
in (match (uu____16562) with
| FStar_Pervasives_Native.None -> begin
(match ((FStar_List.contains HNF cfg.steps)) with
| true -> begin
(

let arg = (closure_as_term cfg env_arg tm)
in (

let t1 = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack2 t1)))
end
| uu____16681 -> begin
(

let stack3 = (MemoLazy (m))::(App (((env), (t), (aq), (r))))::stack2
in (norm cfg env_arg stack3 tm))
end)
end
| FStar_Pervasives_Native.Some (uu____16706, a) -> begin
(

let t1 = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack2 t1))
end))
end);
)
end
| (App (env1, head1, aq, r))::stack2 -> begin
(

let t1 = (FStar_Syntax_Syntax.extend_app head1 ((t), (aq)) FStar_Pervasives_Native.None r)
in (

let uu____16749 = (maybe_simplify cfg env1 stack2 t1)
in (rebuild cfg env1 stack2 uu____16749)))
end
| (Match (env1, branches, r))::stack2 -> begin
((log cfg (fun uu____16761 -> (

let uu____16762 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" uu____16762))));
(

let scrutinee = t
in (

let norm_and_rebuild_match = (fun uu____16767 -> ((log cfg (fun uu____16772 -> (

let uu____16773 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____16774 = (

let uu____16775 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____16792 -> (match (uu____16792) with
| (p, uu____16802, uu____16803) -> begin
(FStar_Syntax_Print.pat_to_string p)
end))))
in (FStar_All.pipe_right uu____16775 (FStar_String.concat "\n\t")))
in (FStar_Util.print2 "match is irreducible: scrutinee=%s\nbranches=%s\n" uu____16773 uu____16774)))));
(

let whnf = ((FStar_List.contains Weak cfg.steps) || (FStar_List.contains HNF cfg.steps))
in (

let cfg_exclude_iota_zeta = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun uu___192_16820 -> (match (uu___192_16820) with
| FStar_TypeChecker_Env.Inlining -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| uu____16821 -> begin
false
end))))
in (

let steps' = (

let uu____16825 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____16825) with
| true -> begin
(Exclude (Zeta))::[]
end
| uu____16828 -> begin
(Exclude (Iota))::(Exclude (Zeta))::[]
end))
in (only_strong_steps (

let uu___253_16831 = cfg
in {steps = (FStar_List.append steps' cfg.steps); tcenv = uu___253_16831.tcenv; delta_level = new_delta; primitive_steps = uu___253_16831.primitive_steps}))))
in (

let norm_or_whnf = (fun env2 t1 -> (match (whnf) with
| true -> begin
(closure_as_term cfg_exclude_iota_zeta env2 t1)
end
| uu____16839 -> begin
(norm cfg_exclude_iota_zeta env2 [] t1)
end))
in (

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____16863) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____16884 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____16944 uu____16945 -> (match (((uu____16944), (uu____16945))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____17036 = (norm_pat env3 p1)
in (match (uu____17036) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____16884) with
| (pats1, env3) -> begin
(((

let uu___254_17118 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___254_17118.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___255_17137 = x
in (

let uu____17138 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___255_17137.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___255_17137.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____17138}))
in (((

let uu___256_17152 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___256_17152.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___257_17163 = x
in (

let uu____17164 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___257_17163.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___257_17163.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____17164}))
in (((

let uu___258_17178 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___258_17178.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t1) -> begin
(

let x1 = (

let uu___259_17194 = x
in (

let uu____17195 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___259_17194.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___259_17194.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____17195}))
in (

let t2 = (norm_or_whnf env2 t1)
in (((

let uu___260_17202 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t2))); FStar_Syntax_Syntax.p = uu___260_17202.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let branches1 = (match (env1) with
| [] when whnf -> begin
branches
end
| uu____17212 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch1 -> (

let uu____17226 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____17226) with
| (p, wopt, e) -> begin
(

let uu____17246 = (norm_pat env1 p)
in (match (uu____17246) with
| (p1, env2) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____17271 = (norm_or_whnf env2 w)
in FStar_Pervasives_Native.Some (uu____17271))
end)
in (

let e1 = (norm_or_whnf env2 e)
in (FStar_Syntax_Util.branch ((p1), (wopt1), (e1)))))
end))
end)))))
end)
in (

let uu____17277 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches1)))) r)
in (rebuild cfg env1 stack2 uu____17277)))))));
))
in (

let rec is_cons = (fun head1 -> (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, uu____17287) -> begin
(is_cons h)
end
| FStar_Syntax_Syntax.Tm_constant (uu____17292) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____17293; FStar_Syntax_Syntax.fv_delta = uu____17294; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____17295; FStar_Syntax_Syntax.fv_delta = uu____17296; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____17297))}) -> begin
true
end
| uu____17304 -> begin
false
end))
in (

let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| FStar_Pervasives_Native.None -> begin
b
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let then_branch = b
in (

let else_branch = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (rest)))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (

let rec matches_pat = (fun scrutinee_orig p -> (

let scrutinee1 = (FStar_Syntax_Util.unmeta scrutinee_orig)
in (

let uu____17449 = (FStar_Syntax_Util.head_and_args scrutinee1)
in (match (uu____17449) with
| (head1, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____17536) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (Prims.op_Equality s s') -> begin
FStar_Util.Inl ([])
end
| uu____17575 -> begin
(

let uu____17576 = (

let uu____17577 = (is_cons head1)
in (not (uu____17577)))
in FStar_Util.Inr (uu____17576))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let uu____17602 = (

let uu____17603 = (FStar_Syntax_Util.un_uinst head1)
in uu____17603.FStar_Syntax_Syntax.n)
in (match (uu____17602) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| uu____17621 -> begin
(

let uu____17622 = (

let uu____17623 = (is_cons head1)
in (not (uu____17623)))
in FStar_Util.Inr (uu____17622))
end))
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t1, uu____17692))::rest_a, ((p1, uu____17695))::rest_p) -> begin
(

let uu____17739 = (matches_pat t1 p1)
in (match (uu____17739) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____17788 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee1 p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p1, wopt, b))::rest -> begin
(

let uu____17894 = (matches_pat scrutinee1 p1)
in (match (uu____17894) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee1 rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
((log cfg (fun uu____17934 -> (

let uu____17935 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____17936 = (

let uu____17937 = (FStar_List.map (fun uu____17947 -> (match (uu____17947) with
| (uu____17952, t1) -> begin
(FStar_Syntax_Print.term_to_string t1)
end)) s)
in (FStar_All.pipe_right uu____17937 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" uu____17935 uu____17936)))));
(

let env2 = (FStar_List.fold_left (fun env2 uu____17983 -> (match (uu____17983) with
| (bv, t1) -> begin
(

let uu____18006 = (

let uu____18013 = (

let uu____18016 = (FStar_Syntax_Syntax.mk_binder bv)
in FStar_Pervasives_Native.Some (uu____18016))
in (

let uu____18017 = (

let uu____18018 = (

let uu____18049 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ((([]), (t1)))))
in (([]), (t1), (uu____18049), (false)))
in Clos (uu____18018))
in ((uu____18013), (uu____18017))))
in (uu____18006)::env2)
end)) env1 s)
in (

let uu____18158 = (guard_when_clause wopt b rest)
in (norm cfg env2 stack2 uu____18158)));
)
end))
end))
in (

let uu____18159 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota))))
in (match (uu____18159) with
| true -> begin
(norm_and_rebuild_match ())
end
| uu____18160 -> begin
(matches scrutinee branches)
end))))))));
)
end);
))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun uu___193_18182 -> (match (uu___193_18182) with
| UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| Inlining -> begin
(FStar_TypeChecker_Env.Inlining)::[]
end
| UnfoldTac -> begin
(FStar_TypeChecker_Env.UnfoldTac)::[]
end
| uu____18186 -> begin
[]
end))))
in (

let d1 = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| uu____18192 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d1; primitive_steps = built_in_primitive_steps})))


let normalize_with_primitive_steps : primitive_step Prims.list  ->  step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun ps s e t -> (

let c = (config s e)
in (

let c1 = (

let uu___261_18221 = (config s e)
in {steps = uu___261_18221.steps; tcenv = uu___261_18221.tcenv; delta_level = uu___261_18221.delta_level; primitive_steps = (FStar_List.append c.primitive_steps ps)})
in (norm c1 [] [] t))))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (normalize_with_primitive_steps [] s e t))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (

let uu____18252 = (config s e)
in (norm_comp uu____18252 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let uu____18267 = (config [] env)
in (norm_universe uu____18267 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (

let uu____18282 = (config [] env)
in (ghost_to_pure_aux uu____18282 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (

let uu____18302 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____18302)))
in (

let uu____18309 = ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ))
in (match (uu____18309) with
| true -> begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let uu___262_18311 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = uu___262_18311.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___262_18311.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____18314 -> (

let uu____18315 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env uu____18315)))})
end
| FStar_Pervasives_Native.None -> begin
lc
end)
end
| uu____18316 -> begin
lc
end)))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (

let t1 = (FStar_All.try_with (fun uu___264_18327 -> (match (()) with
| () -> begin
(normalize ((AllowUnboundUniverses)::[]) env t)
end)) (fun uu___263_18331 -> (match (uu___263_18331) with
| e -> begin
((

let uu____18334 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_warning "Normalization failed with error %s\n" uu____18334));
t;
)
end)))
in (FStar_Syntax_Print.term_to_string t1)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let c1 = (FStar_All.try_with (fun uu___266_18346 -> (match (()) with
| () -> begin
(

let uu____18347 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp uu____18347 [] c))
end)) (fun uu___265_18357 -> (match (uu___265_18357) with
| e -> begin
((

let uu____18360 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_warning "Normalization failed with error %s\n" uu____18360));
c;
)
end)))
in (FStar_Syntax_Print.comp_to_string c1)))


let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (

let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (

let rec aux = (fun t1 -> (

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let t01 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t01.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(

let uu____18400 = (

let uu____18401 = (

let uu____18408 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (uu____18408)))
in FStar_Syntax_Syntax.Tm_refine (uu____18401))
in (mk uu____18400 t01.FStar_Syntax_Syntax.pos))
end
| uu____18413 -> begin
t2
end))
end
| uu____18414 -> begin
t2
end)))
in (aux t))))


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((Weak)::(HNF)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Beta)::[]) env t))


let reduce_or_remove_uvar_solutions : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun remove env t -> (normalize (FStar_List.append (match (remove) with
| true -> begin
(CheckNoUvars)::[]
end
| uu____18437 -> begin
[]
end) ((Beta)::(NoDeltaSteps)::(CompressUvars)::(Exclude (Zeta))::(Exclude (Iota))::(NoFullNorm)::[])) env t))


let reduce_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions false env t))


let remove_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions true env t))


let eta_expand_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e t_e -> (

let uu____18466 = (FStar_Syntax_Util.arrow_formals_comp t_e)
in (match (uu____18466) with
| (formals, c) -> begin
(match (formals) with
| [] -> begin
e
end
| uu____18495 -> begin
(

let uu____18502 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____18502) with
| (actuals, uu____18512, uu____18513) -> begin
(match ((Prims.op_Equality (FStar_List.length actuals) (FStar_List.length formals))) with
| true -> begin
e
end
| uu____18526 -> begin
(

let uu____18527 = (FStar_All.pipe_right formals FStar_Syntax_Util.args_of_binders)
in (match (uu____18527) with
| (binders, args) -> begin
(

let uu____18544 = (FStar_Syntax_Syntax.mk_Tm_app e args FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Util.abs binders uu____18544 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c)))))
end))
end)
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(eta_expand_with_type env t x.FStar_Syntax_Syntax.sort)
end
| uu____18554 -> begin
(

let uu____18555 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____18555) with
| (head1, args) -> begin
(

let uu____18592 = (

let uu____18593 = (FStar_Syntax_Subst.compress head1)
in uu____18593.FStar_Syntax_Syntax.n)
in (match (uu____18592) with
| FStar_Syntax_Syntax.Tm_uvar (uu____18596, thead) -> begin
(

let uu____18622 = (FStar_Syntax_Util.arrow_formals thead)
in (match (uu____18622) with
| (formals, tres) -> begin
(match ((Prims.op_Equality (FStar_List.length formals) (FStar_List.length args))) with
| true -> begin
t
end
| uu____18663 -> begin
(

let uu____18664 = (env.FStar_TypeChecker_Env.type_of (

let uu___267_18672 = env
in {FStar_TypeChecker_Env.solver = uu___267_18672.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___267_18672.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___267_18672.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___267_18672.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___267_18672.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___267_18672.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___267_18672.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___267_18672.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___267_18672.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___267_18672.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___267_18672.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___267_18672.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___267_18672.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___267_18672.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___267_18672.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___267_18672.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___267_18672.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___267_18672.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___267_18672.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___267_18672.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___267_18672.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___267_18672.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___267_18672.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___267_18672.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___267_18672.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___267_18672.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___267_18672.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___267_18672.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___267_18672.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___267_18672.FStar_TypeChecker_Env.dsenv}) t)
in (match (uu____18664) with
| (uu____18673, ty, uu____18675) -> begin
(eta_expand_with_type env t ty)
end))
end)
end))
end
| uu____18676 -> begin
(

let uu____18677 = (env.FStar_TypeChecker_Env.type_of (

let uu___268_18685 = env
in {FStar_TypeChecker_Env.solver = uu___268_18685.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___268_18685.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___268_18685.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___268_18685.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___268_18685.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___268_18685.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___268_18685.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___268_18685.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___268_18685.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___268_18685.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___268_18685.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___268_18685.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___268_18685.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___268_18685.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___268_18685.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___268_18685.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___268_18685.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___268_18685.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___268_18685.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___268_18685.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___268_18685.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___268_18685.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___268_18685.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___268_18685.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___268_18685.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___268_18685.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___268_18685.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___268_18685.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___268_18685.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___268_18685.FStar_TypeChecker_Env.dsenv}) t)
in (match (uu____18677) with
| (uu____18686, ty, uu____18688) -> begin
(eta_expand_with_type env t ty)
end))
end))
end))
end))


let elim_uvars_aux_tc : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.comp) FStar_Util.either  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either) = (fun env univ_names binders tc -> (

let t = (match (((binders), (tc))) with
| ([], FStar_Util.Inl (t)) -> begin
t
end
| ([], FStar_Util.Inr (c)) -> begin
(failwith "Impossible: empty bindes with a comp")
end
| (uu____18766, FStar_Util.Inr (c)) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
end
| (uu____18772, FStar_Util.Inl (t)) -> begin
(

let uu____18778 = (

let uu____18781 = (

let uu____18782 = (

let uu____18795 = (FStar_Syntax_Syntax.mk_Total t)
in ((binders), (uu____18795)))
in FStar_Syntax_Syntax.Tm_arrow (uu____18782))
in (FStar_Syntax_Syntax.mk uu____18781))
in (uu____18778 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end)
in (

let uu____18799 = (FStar_Syntax_Subst.open_univ_vars univ_names t)
in (match (uu____18799) with
| (univ_names1, t1) -> begin
(

let t2 = (remove_uvar_solutions env t1)
in (

let t3 = (FStar_Syntax_Subst.close_univ_vars univ_names1 t2)
in (

let uu____18826 = (match (binders) with
| [] -> begin
(([]), (FStar_Util.Inl (t3)))
end
| uu____18881 -> begin
(

let uu____18882 = (

let uu____18891 = (

let uu____18892 = (FStar_Syntax_Subst.compress t3)
in uu____18892.FStar_Syntax_Syntax.n)
in ((uu____18891), (tc)))
in (match (uu____18882) with
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inr (uu____18917)) -> begin
((binders1), (FStar_Util.Inr (c)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inl (uu____18954)) -> begin
((binders1), (FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))))
end
| (uu____18993, FStar_Util.Inl (uu____18994)) -> begin
(([]), (FStar_Util.Inl (t3)))
end
| uu____19017 -> begin
(failwith "Impossible")
end))
end)
in (match (uu____18826) with
| (binders1, tc1) -> begin
((univ_names1), (binders1), (tc1))
end))))
end))))


let elim_uvars_aux_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term) = (fun env univ_names binders t -> (

let uu____19126 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl (t)))
in (match (uu____19126) with
| (univ_names1, binders1, tc) -> begin
(

let uu____19184 = (FStar_Util.left tc)
in ((univ_names1), (binders1), (uu____19184)))
end)))


let elim_uvars_aux_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) = (fun env univ_names binders c -> (

let uu____19223 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr (c)))
in (match (uu____19223) with
| (univ_names1, binders1, tc) -> begin
(

let uu____19283 = (FStar_Util.right tc)
in ((univ_names1), (binders1), (uu____19283)))
end)))


let rec elim_uvars : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, lids, lids') -> begin
(

let uu____19318 = (elim_uvars_aux_t env univ_names binders typ)
in (match (uu____19318) with
| (univ_names1, binders1, typ1) -> begin
(

let uu___269_19346 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univ_names1), (binders1), (typ1), (lids), (lids'))); FStar_Syntax_Syntax.sigrng = uu___269_19346.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___269_19346.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___269_19346.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___269_19346.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uu___270_19367 = s
in (

let uu____19368 = (

let uu____19369 = (

let uu____19378 = (FStar_List.map (elim_uvars env) sigs)
in ((uu____19378), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____19369))
in {FStar_Syntax_Syntax.sigel = uu____19368; FStar_Syntax_Syntax.sigrng = uu___270_19367.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___270_19367.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___270_19367.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___270_19367.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univ_names, typ, lident, i, lids) -> begin
(

let uu____19395 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____19395) with
| (univ_names1, uu____19413, typ1) -> begin
(

let uu___271_19427 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univ_names1), (typ1), (lident), (i), (lids))); FStar_Syntax_Syntax.sigrng = uu___271_19427.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___271_19427.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___271_19427.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___271_19427.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) -> begin
(

let uu____19433 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____19433) with
| (univ_names1, uu____19451, typ1) -> begin
(

let uu___272_19465 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (univ_names1), (typ1))); FStar_Syntax_Syntax.sigrng = uu___272_19465.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___272_19465.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___272_19465.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___272_19465.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____19499 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____19499) with
| (opening, lbunivs) -> begin
(

let elim = (fun t -> (

let uu____19522 = (

let uu____19523 = (FStar_Syntax_Subst.subst opening t)
in (remove_uvar_solutions env uu____19523))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____19522)))
in (

let lbtyp = (elim lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (elim lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___273_19526 = lb
in {FStar_Syntax_Syntax.lbname = uu___273_19526.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___273_19526.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}))))
end)))))
in (

let uu___274_19527 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((b), (lbs1))), (lids))); FStar_Syntax_Syntax.sigrng = uu___274_19527.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___274_19527.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___274_19527.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___274_19527.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(

let uu___275_19539 = s
in (

let uu____19540 = (

let uu____19541 = (remove_uvar_solutions env t)
in FStar_Syntax_Syntax.Sig_main (uu____19541))
in {FStar_Syntax_Syntax.sigel = uu____19540; FStar_Syntax_Syntax.sigrng = uu___275_19539.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___275_19539.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___275_19539.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___275_19539.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, t) -> begin
(

let uu____19545 = (elim_uvars_aux_t env us [] t)
in (match (uu____19545) with
| (us1, uu____19563, t1) -> begin
(

let uu___276_19577 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((l), (us1), (t1))); FStar_Syntax_Syntax.sigrng = uu___276_19577.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___276_19577.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___276_19577.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___276_19577.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____19578) -> begin
(failwith "Impossible: should have been desugared already")
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____19580 = (elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____19580) with
| (univs1, binders, signature) -> begin
(

let uu____19608 = (

let uu____19617 = (FStar_Syntax_Subst.univ_var_opening univs1)
in (match (uu____19617) with
| (univs_opening, univs2) -> begin
(

let uu____19644 = (FStar_Syntax_Subst.univ_var_closing univs2)
in ((univs_opening), (uu____19644)))
end))
in (match (uu____19608) with
| (univs_opening, univs_closing) -> begin
(

let uu____19661 = (

let binders1 = (FStar_Syntax_Subst.open_binders binders)
in (

let uu____19667 = (FStar_Syntax_Subst.opening_of_binders binders1)
in (

let uu____19668 = (FStar_Syntax_Subst.closing_of_binders binders1)
in ((uu____19667), (uu____19668)))))
in (match (uu____19661) with
| (b_opening, b_closing) -> begin
(

let n1 = (FStar_List.length univs1)
in (

let n_binders = (FStar_List.length binders)
in (

let elim_tscheme = (fun uu____19690 -> (match (uu____19690) with
| (us, t) -> begin
(

let n_us = (FStar_List.length us)
in (

let uu____19708 = (FStar_Syntax_Subst.open_univ_vars us t)
in (match (uu____19708) with
| (us1, t1) -> begin
(

let uu____19719 = (

let uu____19724 = (FStar_All.pipe_right b_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____19731 = (FStar_All.pipe_right b_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____19724), (uu____19731))))
in (match (uu____19719) with
| (b_opening1, b_closing1) -> begin
(

let uu____19744 = (

let uu____19749 = (FStar_All.pipe_right univs_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____19758 = (FStar_All.pipe_right univs_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____19749), (uu____19758))))
in (match (uu____19744) with
| (univs_opening1, univs_closing1) -> begin
(

let t2 = (

let uu____19774 = (FStar_Syntax_Subst.subst b_opening1 t1)
in (FStar_Syntax_Subst.subst univs_opening1 uu____19774))
in (

let uu____19775 = (elim_uvars_aux_t env [] [] t2)
in (match (uu____19775) with
| (uu____19796, uu____19797, t3) -> begin
(

let t4 = (

let uu____19812 = (

let uu____19813 = (FStar_Syntax_Subst.close_univ_vars us1 t3)
in (FStar_Syntax_Subst.subst b_closing1 uu____19813))
in (FStar_Syntax_Subst.subst univs_closing1 uu____19812))
in ((us1), (t4)))
end)))
end))
end))
end)))
end))
in (

let elim_term = (fun t -> (

let uu____19818 = (elim_uvars_aux_t env univs1 binders t)
in (match (uu____19818) with
| (uu____19831, uu____19832, t1) -> begin
t1
end)))
in (

let elim_action = (fun a -> (

let action_typ_templ = (

let body = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((a.FStar_Syntax_Syntax.action_defn), (((FStar_Util.Inl (a.FStar_Syntax_Syntax.action_typ)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (match (a.FStar_Syntax_Syntax.action_params) with
| [] -> begin
body
end
| uu____19892 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((a.FStar_Syntax_Syntax.action_params), (body), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
end))
in (

let destruct_action_body = (fun body -> (

let uu____19909 = (

let uu____19910 = (FStar_Syntax_Subst.compress body)
in uu____19910.FStar_Syntax_Syntax.n)
in (match (uu____19909) with
| FStar_Syntax_Syntax.Tm_ascribed (defn, (FStar_Util.Inl (typ), FStar_Pervasives_Native.None), FStar_Pervasives_Native.None) -> begin
((defn), (typ))
end
| uu____19969 -> begin
(failwith "Impossible")
end)))
in (

let destruct_action_typ_templ = (fun t -> (

let uu____19998 = (

let uu____19999 = (FStar_Syntax_Subst.compress t)
in uu____19999.FStar_Syntax_Syntax.n)
in (match (uu____19998) with
| FStar_Syntax_Syntax.Tm_abs (pars, body, uu____20020) -> begin
(

let uu____20041 = (destruct_action_body body)
in (match (uu____20041) with
| (defn, typ) -> begin
((pars), (defn), (typ))
end))
end
| uu____20086 -> begin
(

let uu____20087 = (destruct_action_body t)
in (match (uu____20087) with
| (defn, typ) -> begin
(([]), (defn), (typ))
end))
end)))
in (

let uu____20136 = (elim_tscheme ((a.FStar_Syntax_Syntax.action_univs), (action_typ_templ)))
in (match (uu____20136) with
| (action_univs, t) -> begin
(

let uu____20145 = (destruct_action_typ_templ t)
in (match (uu____20145) with
| (action_params, action_defn, action_typ) -> begin
(

let a' = (

let uu___277_20186 = a
in {FStar_Syntax_Syntax.action_name = uu___277_20186.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___277_20186.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action_univs; FStar_Syntax_Syntax.action_params = action_params; FStar_Syntax_Syntax.action_defn = action_defn; FStar_Syntax_Syntax.action_typ = action_typ})
in a')
end))
end))))))
in (

let ed1 = (

let uu___278_20188 = ed
in (

let uu____20189 = (elim_tscheme ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____20190 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____20191 = (elim_tscheme ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____20192 = (elim_tscheme ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____20193 = (elim_tscheme ed.FStar_Syntax_Syntax.stronger)
in (

let uu____20194 = (elim_tscheme ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____20195 = (elim_tscheme ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____20196 = (elim_tscheme ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____20197 = (elim_tscheme ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____20198 = (elim_tscheme ed.FStar_Syntax_Syntax.trivial)
in (

let uu____20199 = (elim_term ed.FStar_Syntax_Syntax.repr)
in (

let uu____20200 = (elim_tscheme ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____20201 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____20202 = (FStar_List.map elim_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___278_20188.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___278_20188.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu____20189; FStar_Syntax_Syntax.bind_wp = uu____20190; FStar_Syntax_Syntax.if_then_else = uu____20191; FStar_Syntax_Syntax.ite_wp = uu____20192; FStar_Syntax_Syntax.stronger = uu____20193; FStar_Syntax_Syntax.close_wp = uu____20194; FStar_Syntax_Syntax.assert_p = uu____20195; FStar_Syntax_Syntax.assume_p = uu____20196; FStar_Syntax_Syntax.null_wp = uu____20197; FStar_Syntax_Syntax.trivial = uu____20198; FStar_Syntax_Syntax.repr = uu____20199; FStar_Syntax_Syntax.return_repr = uu____20200; FStar_Syntax_Syntax.bind_repr = uu____20201; FStar_Syntax_Syntax.actions = uu____20202})))))))))))))))
in (

let uu___279_20205 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ed1); FStar_Syntax_Syntax.sigrng = uu___279_20205.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___279_20205.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___279_20205.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___279_20205.FStar_Syntax_Syntax.sigattrs})))))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub_eff) -> begin
(

let elim_tscheme_opt = (fun uu___194_20222 -> (match (uu___194_20222) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (us, t) -> begin
(

let uu____20249 = (elim_uvars_aux_t env us [] t)
in (match (uu____20249) with
| (us1, uu____20273, t1) -> begin
FStar_Pervasives_Native.Some (((us1), (t1)))
end))
end))
in (

let sub_eff1 = (

let uu___280_20292 = sub_eff
in (

let uu____20293 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp)
in (

let uu____20296 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift)
in {FStar_Syntax_Syntax.source = uu___280_20292.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___280_20292.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = uu____20293; FStar_Syntax_Syntax.lift = uu____20296})))
in (

let uu___281_20299 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub_eff1); FStar_Syntax_Syntax.sigrng = uu___281_20299.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___281_20299.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___281_20299.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___281_20299.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univ_names, binders, comp, flags) -> begin
(

let uu____20309 = (elim_uvars_aux_c env univ_names binders comp)
in (match (uu____20309) with
| (univ_names1, binders1, comp1) -> begin
(

let uu___282_20343 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (univ_names1), (binders1), (comp1), (flags))); FStar_Syntax_Syntax.sigrng = uu___282_20343.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___282_20343.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___282_20343.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___282_20343.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_pragma (uu____20354) -> begin
s
end))




