
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
in (FStar_List.map (fun _0_42 -> FStar_Syntax_Syntax.U_succ (_0_42)) uu____1906))
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
in {FStar_Syntax_Syntax.ppname = uu___202_2988.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___202_2988.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty}) (fun _0_43 -> FStar_Util.Inl (_0_43))))
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

let uu____4246 = (FStar_Util.int_of_string i)
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
in (FStar_Syntax_Embeddings.embed_int rng r)))
in (

let string_concat' = (fun psc args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____4702 = (arg_as_string a1)
in (match (uu____4702) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____4708 = (arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2)
in (match (uu____4708) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.concat s1 s2)
in (

let uu____4721 = (FStar_Syntax_Embeddings.embed_string psc.psc_range r)
in FStar_Pervasives_Native.Some (uu____4721)))
end
| uu____4722 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4727 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4730 -> begin
FStar_Pervasives_Native.None
end))
in (

let string_of_int1 = (fun rng i -> (

let uu____4740 = (FStar_Util.string_of_int i)
in (FStar_Syntax_Embeddings.embed_string rng uu____4740)))
in (

let string_of_bool1 = (fun rng b -> (FStar_Syntax_Embeddings.embed_string rng (match (b) with
| true -> begin
"true"
end
| uu____4748 -> begin
"false"
end)))
in (

let string_of_int2 = (fun rng i -> (

let uu____4756 = (FStar_Util.string_of_int i)
in (FStar_Syntax_Embeddings.embed_string rng uu____4756)))
in (

let string_of_bool2 = (fun rng b -> (FStar_Syntax_Embeddings.embed_string rng (match (b) with
| true -> begin
"true"
end
| uu____4764 -> begin
"false"
end)))
in (

let term_of_range = (fun r -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r))) FStar_Pervasives_Native.None r))
in (

let range_of1 = (fun uu____4786 args -> (match (args) with
| (uu____4798)::((t, uu____4800))::[] -> begin
(

let uu____4829 = (term_of_range t.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (uu____4829))
end
| uu____4834 -> begin
FStar_Pervasives_Native.None
end))
in (

let set_range_of1 = (fun uu____4856 args -> (match (args) with
| (uu____4866)::((t, uu____4868))::((r, uu____4870))::[] -> begin
(

let uu____4891 = (FStar_Syntax_Embeddings.unembed_range_safe r)
in (FStar_Util.bind_opt uu____4891 (fun r1 -> FStar_Pervasives_Native.Some ((

let uu___214_4901 = t
in {FStar_Syntax_Syntax.n = uu___214_4901.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___214_4901.FStar_Syntax_Syntax.vars})))))
end
| uu____4902 -> begin
FStar_Pervasives_Native.None
end))
in (

let mk_range1 = (fun uu____4918 args -> (match (args) with
| (fn)::(from_line)::(from_col)::(to_line)::(to_col)::[] -> begin
(

let uu____4929 = (

let uu____4950 = (arg_as_string fn)
in (

let uu____4953 = (arg_as_int from_line)
in (

let uu____4956 = (arg_as_int from_col)
in (

let uu____4959 = (arg_as_int to_line)
in (

let uu____4962 = (arg_as_int to_col)
in ((uu____4950), (uu____4953), (uu____4956), (uu____4959), (uu____4962)))))))
in (match (uu____4929) with
| (FStar_Pervasives_Native.Some (fn1), FStar_Pervasives_Native.Some (from_l), FStar_Pervasives_Native.Some (from_c), FStar_Pervasives_Native.Some (to_l), FStar_Pervasives_Native.Some (to_c)) -> begin
(

let r = (

let uu____4993 = (FStar_Range.mk_pos from_l from_c)
in (

let uu____4994 = (FStar_Range.mk_pos to_l to_c)
in (FStar_Range.mk_range fn1 uu____4993 uu____4994)))
in (

let uu____4995 = (term_of_range r)
in FStar_Pervasives_Native.Some (uu____4995)))
end
| uu____5000 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____5021 -> begin
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
| ((_typ, uu____5048))::((a1, uu____5050))::((a2, uu____5052))::[] -> begin
(

let uu____5089 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____5089) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
fal
end
| uu____5096 -> begin
tru
end))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
tru
end
| uu____5101 -> begin
fal
end))
end
| uu____5102 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____5103 -> begin
(failwith "Unexpected number of arguments")
end)))))
in (

let basic_ops = (

let uu____5121 = (

let uu____5136 = (

let uu____5151 = (

let uu____5166 = (

let uu____5181 = (

let uu____5196 = (

let uu____5211 = (

let uu____5226 = (

let uu____5241 = (

let uu____5256 = (

let uu____5271 = (

let uu____5286 = (

let uu____5301 = (

let uu____5316 = (

let uu____5331 = (

let uu____5346 = (

let uu____5361 = (

let uu____5376 = (

let uu____5391 = (

let uu____5406 = (

let uu____5421 = (

let uu____5434 = (FStar_Parser_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((uu____5434), ((Prims.parse_int "1")), ((unary_op arg_as_string list_of_string'))))
in (

let uu____5441 = (

let uu____5456 = (

let uu____5469 = (FStar_Parser_Const.p2l (("FStar")::("String")::("string_of_list")::[]))
in ((uu____5469), ((Prims.parse_int "1")), ((unary_op (arg_as_list FStar_Syntax_Embeddings.unembed_char_safe) string_of_list'))))
in (

let uu____5478 = (

let uu____5493 = (

let uu____5508 = (FStar_Parser_Const.p2l (("FStar")::("String")::("concat")::[]))
in ((uu____5508), ((Prims.parse_int "2")), (string_concat')))
in (

let uu____5517 = (

let uu____5534 = (

let uu____5555 = (FStar_Parser_Const.p2l (("Prims")::("range_of")::[]))
in ((uu____5555), ((Prims.parse_int "2")), (range_of1)))
in (

let uu____5570 = (

let uu____5593 = (

let uu____5612 = (FStar_Parser_Const.p2l (("Prims")::("set_range_of")::[]))
in ((uu____5612), ((Prims.parse_int "3")), (set_range_of1)))
in (

let uu____5625 = (

let uu____5646 = (

let uu____5661 = (FStar_Parser_Const.p2l (("Prims")::("mk_range")::[]))
in ((uu____5661), ((Prims.parse_int "5")), (mk_range1)))
in (uu____5646)::[])
in (uu____5593)::uu____5625))
in (uu____5534)::uu____5570))
in (uu____5493)::uu____5517))
in (uu____5456)::uu____5478))
in (uu____5421)::uu____5441))
in (((FStar_Parser_Const.op_notEq), ((Prims.parse_int "3")), ((decidable_eq true))))::uu____5406)
in (((FStar_Parser_Const.op_Eq), ((Prims.parse_int "3")), ((decidable_eq false))))::uu____5391)
in (((FStar_Parser_Const.string_compare), ((Prims.parse_int "2")), ((binary_op arg_as_string string_compare'))))::uu____5376)
in (((FStar_Parser_Const.string_of_bool_lid), ((Prims.parse_int "1")), ((unary_op arg_as_bool string_of_bool2))))::uu____5361)
in (((FStar_Parser_Const.string_of_int_lid), ((Prims.parse_int "1")), ((unary_op arg_as_int string_of_int2))))::uu____5346)
in (((FStar_Parser_Const.strcat_lid'), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____5331)
in (((FStar_Parser_Const.strcat_lid), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____5316)
in (((FStar_Parser_Const.op_Or), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x || y))))))::uu____5301)
in (((FStar_Parser_Const.op_And), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x && y))))))::uu____5286)
in (((FStar_Parser_Const.op_Negation), ((Prims.parse_int "1")), ((unary_bool_op (fun x -> (not (x)))))))::uu____5271)
in (((FStar_Parser_Const.op_Modulus), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x mod y))))))::uu____5256)
in (((FStar_Parser_Const.op_GTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (FStar_Syntax_Embeddings.embed_bool r (x >= y)))))))::uu____5241)
in (((FStar_Parser_Const.op_GT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (FStar_Syntax_Embeddings.embed_bool r (x > y)))))))::uu____5226)
in (((FStar_Parser_Const.op_LTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (FStar_Syntax_Embeddings.embed_bool r (x <= y)))))))::uu____5211)
in (((FStar_Parser_Const.op_LT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (FStar_Syntax_Embeddings.embed_bool r (x < y)))))))::uu____5196)
in (((FStar_Parser_Const.op_Division), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x / y))))))::uu____5181)
in (((FStar_Parser_Const.op_Multiply), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x * y))))))::uu____5166)
in (((FStar_Parser_Const.op_Subtraction), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x - y))))))::uu____5151)
in (((FStar_Parser_Const.op_Addition), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x + y))))))::uu____5136)
in (((FStar_Parser_Const.op_Minus), ((Prims.parse_int "1")), ((unary_int_op (fun x -> (~- (x)))))))::uu____5121)
in (

let bounded_arith_ops = (

let bounded_int_types = ("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]
in (

let int_as_bounded = (fun r int_to_t1 n1 -> (

let c = (FStar_Syntax_Embeddings.embed_int r n1)
in (

let int_to_t2 = (FStar_Syntax_Syntax.fv_to_tm int_to_t1)
in (

let uu____6250 = (

let uu____6251 = (

let uu____6252 = (FStar_Syntax_Syntax.as_arg c)
in (uu____6252)::[])
in (FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6251))
in (uu____6250 FStar_Pervasives_Native.None r)))))
in (FStar_All.pipe_right bounded_int_types (FStar_List.collect (fun m -> (

let uu____6287 = (

let uu____6300 = (FStar_Parser_Const.p2l (("FStar")::(m)::("add")::[]))
in ((uu____6300), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____6319 uu____6320 -> (match (((uu____6319), (uu____6320))) with
| ((int_to_t1, x), (uu____6339, y)) -> begin
(int_as_bounded r int_to_t1 (x + y))
end))))))
in (

let uu____6349 = (

let uu____6364 = (

let uu____6377 = (FStar_Parser_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((uu____6377), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____6396 uu____6397 -> (match (((uu____6396), (uu____6397))) with
| ((int_to_t1, x), (uu____6416, y)) -> begin
(int_as_bounded r int_to_t1 (x - y))
end))))))
in (

let uu____6426 = (

let uu____6441 = (

let uu____6454 = (FStar_Parser_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((uu____6454), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____6473 uu____6474 -> (match (((uu____6473), (uu____6474))) with
| ((int_to_t1, x), (uu____6493, y)) -> begin
(int_as_bounded r int_to_t1 (x * y))
end))))))
in (uu____6441)::[])
in (uu____6364)::uu____6426))
in (uu____6287)::uu____6349)))))))
in (FStar_List.map as_primitive_step (FStar_List.append basic_ops bounded_arith_ops)))))))))))))))))))))))))))))))))


let equality_ops : primitive_step Prims.list = (

let interp_prop = (fun psc args -> (

let r = psc.psc_range
in (match (args) with
| ((_typ, uu____6592))::((a1, uu____6594))::((a2, uu____6596))::[] -> begin
(

let uu____6633 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____6633) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___215_6639 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___215_6639.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___215_6639.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___216_6643 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___216_6643.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___216_6643.FStar_Syntax_Syntax.vars}))
end
| uu____6644 -> begin
FStar_Pervasives_Native.None
end))
end
| ((_typ, uu____6646))::(uu____6647)::((a1, uu____6649))::((a2, uu____6651))::[] -> begin
(

let uu____6700 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____6700) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___215_6706 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___215_6706.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___215_6706.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___216_6710 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___216_6710.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___216_6710.FStar_Syntax_Syntax.vars}))
end
| uu____6711 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____6712 -> begin
(failwith "Unexpected number of arguments")
end)))
in (

let propositional_equality = {name = FStar_Parser_Const.eq2_lid; arity = (Prims.parse_int "3"); strong_reduction_ok = true; requires_binder_substitution = false; interpretation = interp_prop}
in (

let hetero_propositional_equality = {name = FStar_Parser_Const.eq3_lid; arity = (Prims.parse_int "4"); strong_reduction_ok = true; requires_binder_substitution = false; interpretation = interp_prop}
in (propositional_equality)::(hetero_propositional_equality)::[])))


let unembed_binder : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option = (fun t -> (FStar_All.try_with (fun uu___218_6729 -> (match (()) with
| () -> begin
(

let uu____6732 = (

let uu____6733 = (FStar_Syntax_Util.un_alien t)
in (FStar_All.pipe_right uu____6733 FStar_Dyn.undyn))
in FStar_Pervasives_Native.Some (uu____6732))
end)) (fun uu___217_6736 -> (match (uu___217_6736) with
| uu____6739 -> begin
FStar_Pervasives_Native.None
end))))


let mk_psc_subst : 'Auu____6746 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____6746) FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun cfg env -> (FStar_List.fold_right (fun uu____6806 subst1 -> (match (uu____6806) with
| (binder_opt, closure) -> begin
(match (((binder_opt), (closure))) with
| (FStar_Pervasives_Native.Some (b), Clos (env1, term, memo, uu____6848)) -> begin
(

let uu____6907 = b
in (match (uu____6907) with
| (bv, uu____6915) -> begin
(

let uu____6916 = (

let uu____6917 = (FStar_Syntax_Util.is_constructed_typ bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.fstar_reflection_types_binder_lid)
in (not (uu____6917)))
in (match (uu____6916) with
| true -> begin
subst1
end
| uu____6920 -> begin
(

let term1 = (closure_as_term cfg env1 term)
in (

let uu____6922 = (unembed_binder term1)
in (match (uu____6922) with
| FStar_Pervasives_Native.None -> begin
subst1
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let b1 = (

let uu____6929 = (

let uu___219_6930 = bv
in (

let uu____6931 = (FStar_Syntax_Subst.subst subst1 (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___219_6930.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___219_6930.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6931}))
in (FStar_Syntax_Syntax.freshen_bv uu____6929))
in (

let b_for_x = (

let uu____6935 = (

let uu____6942 = (FStar_Syntax_Syntax.bv_to_name b1)
in (((FStar_Pervasives_Native.fst x)), (uu____6942)))
in FStar_Syntax_Syntax.NT (uu____6935))
in (

let subst2 = (FStar_List.filter (fun uu___184_6951 -> (match (uu___184_6951) with
| FStar_Syntax_Syntax.NT (uu____6952, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (b'); FStar_Syntax_Syntax.pos = uu____6954; FStar_Syntax_Syntax.vars = uu____6955}) -> begin
(not ((FStar_Ident.ident_equals b1.FStar_Syntax_Syntax.ppname b'.FStar_Syntax_Syntax.ppname)))
end
| uu____6960 -> begin
true
end)) subst1)
in (b_for_x)::subst2)))
end)))
end))
end))
end
| uu____6961 -> begin
subst1
end)
end)) env []))


let reduce_primops : 'Auu____6984 'Auu____6985 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____6985) FStar_Pervasives_Native.option * closure) Prims.list  ->  'Auu____6984  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 tm -> (

let uu____7026 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops cfg.steps))
in (match (uu____7026) with
| true -> begin
tm
end
| uu____7027 -> begin
(

let uu____7028 = (FStar_Syntax_Util.head_and_args tm)
in (match (uu____7028) with
| (head1, args) -> begin
(

let uu____7065 = (

let uu____7066 = (FStar_Syntax_Util.un_uinst head1)
in uu____7066.FStar_Syntax_Syntax.n)
in (match (uu____7065) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____7070 = (FStar_List.tryFind (fun ps -> (FStar_Syntax_Syntax.fv_eq_lid fv ps.name)) cfg.primitive_steps)
in (match (uu____7070) with
| FStar_Pervasives_Native.None -> begin
tm
end
| FStar_Pervasives_Native.Some (prim_step) -> begin
(match (((FStar_List.length args) < prim_step.arity)) with
| true -> begin
((log_primops cfg (fun uu____7087 -> (

let uu____7088 = (FStar_Syntax_Print.lid_to_string prim_step.name)
in (

let uu____7089 = (FStar_Util.string_of_int (FStar_List.length args))
in (

let uu____7096 = (FStar_Util.string_of_int prim_step.arity)
in (FStar_Util.print3 "primop: found partially applied %s (%s/%s args)\n" uu____7088 uu____7089 uu____7096))))));
tm;
)
end
| uu____7097 -> begin
((log_primops cfg (fun uu____7101 -> (

let uu____7102 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: trying to reduce <%s>\n" uu____7102))));
(

let psc = {psc_range = head1.FStar_Syntax_Syntax.pos; psc_subst = (fun uu____7105 -> (match (prim_step.requires_binder_substitution) with
| true -> begin
(mk_psc_subst cfg env)
end
| uu____7106 -> begin
[]
end))}
in (

let uu____7107 = (prim_step.interpretation psc args)
in (match (uu____7107) with
| FStar_Pervasives_Native.None -> begin
((log_primops cfg (fun uu____7113 -> (

let uu____7114 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: <%s> did not reduce\n" uu____7114))));
tm;
)
end
| FStar_Pervasives_Native.Some (reduced) -> begin
((log_primops cfg (fun uu____7120 -> (

let uu____7121 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____7122 = (FStar_Syntax_Print.term_to_string reduced)
in (FStar_Util.print2 "primop: <%s> reduced to <%s>\n" uu____7121 uu____7122)))));
reduced;
)
end)));
)
end)
end))
end
| uu____7123 -> begin
tm
end))
end))
end)))


let reduce_equality : 'Auu____7134 'Auu____7135 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____7135) FStar_Pervasives_Native.option * closure) Prims.list  ->  'Auu____7134  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (reduce_primops (

let uu___220_7173 = cfg
in {steps = (Primops)::[]; tcenv = uu___220_7173.tcenv; delta_level = uu___220_7173.delta_level; primitive_steps = equality_ops}) tm))


let maybe_simplify : 'Auu____7186 'Auu____7187 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____7187) FStar_Pervasives_Native.option * closure) Prims.list  ->  'Auu____7186  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 tm -> (

let tm1 = (reduce_primops cfg env stack1 tm)
in (

let uu____7229 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify cfg.steps))
in (match (uu____7229) with
| true -> begin
tm1
end
| uu____7230 -> begin
(

let w = (fun t -> (

let uu___221_7241 = t
in {FStar_Syntax_Syntax.n = uu___221_7241.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = tm1.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___221_7241.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_Pervasives_Native.Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid) -> begin
FStar_Pervasives_Native.Some (false)
end
| uu____7258 -> begin
FStar_Pervasives_Native.None
end))
in (

let simplify1 = (fun arg -> (((simp_t (FStar_Pervasives_Native.fst arg))), (arg)))
in (match (tm1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7298; FStar_Syntax_Syntax.vars = uu____7299}, uu____7300); FStar_Syntax_Syntax.pos = uu____7301; FStar_Syntax_Syntax.vars = uu____7302}, args) -> begin
(

let uu____7328 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____7328) with
| true -> begin
(

let uu____7329 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____7329) with
| ((FStar_Pervasives_Native.Some (true), uu____7384))::((uu____7385, (arg, uu____7387)))::[] -> begin
arg
end
| ((uu____7452, (arg, uu____7454)))::((FStar_Pervasives_Native.Some (true), uu____7455))::[] -> begin
arg
end
| ((FStar_Pervasives_Native.Some (false), uu____7520))::(uu____7521)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____7584)::((FStar_Pervasives_Native.Some (false), uu____7585))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____7648 -> begin
tm1
end))
end
| uu____7663 -> begin
(

let uu____7664 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____7664) with
| true -> begin
(

let uu____7665 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____7665) with
| ((FStar_Pervasives_Native.Some (true), uu____7720))::(uu____7721)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____7784)::((FStar_Pervasives_Native.Some (true), uu____7785))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____7848))::((uu____7849, (arg, uu____7851)))::[] -> begin
arg
end
| ((uu____7916, (arg, uu____7918)))::((FStar_Pervasives_Native.Some (false), uu____7919))::[] -> begin
arg
end
| uu____7984 -> begin
tm1
end))
end
| uu____7999 -> begin
(

let uu____8000 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____8000) with
| true -> begin
(

let uu____8001 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____8001) with
| (uu____8056)::((FStar_Pervasives_Native.Some (true), uu____8057))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____8120))::(uu____8121)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____8184))::((uu____8185, (arg, uu____8187)))::[] -> begin
arg
end
| ((uu____8252, (p, uu____8254)))::((uu____8255, (q, uu____8257)))::[] -> begin
(

let uu____8322 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____8322) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____8323 -> begin
tm1
end))
end
| uu____8324 -> begin
tm1
end))
end
| uu____8339 -> begin
(

let uu____8340 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____8340) with
| true -> begin
(

let uu____8341 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____8341) with
| ((FStar_Pervasives_Native.Some (true), uu____8396))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____8435))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____8474 -> begin
tm1
end))
end
| uu____8489 -> begin
(

let uu____8490 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____8490) with
| true -> begin
(match (args) with
| ((t, uu____8492))::[] -> begin
(

let uu____8509 = (

let uu____8510 = (FStar_Syntax_Subst.compress t)
in uu____8510.FStar_Syntax_Syntax.n)
in (match (uu____8509) with
| FStar_Syntax_Syntax.Tm_abs ((uu____8513)::[], body, uu____8515) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____8542 -> begin
tm1
end)
end
| uu____8545 -> begin
tm1
end))
end
| ((uu____8546, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____8547))))::((t, uu____8549))::[] -> begin
(

let uu____8588 = (

let uu____8589 = (FStar_Syntax_Subst.compress t)
in uu____8589.FStar_Syntax_Syntax.n)
in (match (uu____8588) with
| FStar_Syntax_Syntax.Tm_abs ((uu____8592)::[], body, uu____8594) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____8621 -> begin
tm1
end)
end
| uu____8624 -> begin
tm1
end))
end
| uu____8625 -> begin
tm1
end)
end
| uu____8634 -> begin
(

let uu____8635 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____8635) with
| true -> begin
(match (args) with
| ((t, uu____8637))::[] -> begin
(

let uu____8654 = (

let uu____8655 = (FStar_Syntax_Subst.compress t)
in uu____8655.FStar_Syntax_Syntax.n)
in (match (uu____8654) with
| FStar_Syntax_Syntax.Tm_abs ((uu____8658)::[], body, uu____8660) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____8687 -> begin
tm1
end)
end
| uu____8690 -> begin
tm1
end))
end
| ((uu____8691, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____8692))))::((t, uu____8694))::[] -> begin
(

let uu____8733 = (

let uu____8734 = (FStar_Syntax_Subst.compress t)
in uu____8734.FStar_Syntax_Syntax.n)
in (match (uu____8733) with
| FStar_Syntax_Syntax.Tm_abs ((uu____8737)::[], body, uu____8739) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____8766 -> begin
tm1
end)
end
| uu____8769 -> begin
tm1
end))
end
| uu____8770 -> begin
tm1
end)
end
| uu____8779 -> begin
(

let uu____8780 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
in (match (uu____8780) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____8781; FStar_Syntax_Syntax.vars = uu____8782}, uu____8783))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____8800; FStar_Syntax_Syntax.vars = uu____8801}, uu____8802))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____8819 -> begin
tm1
end)
end
| uu____8828 -> begin
(reduce_equality cfg env stack1 tm1)
end))
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8830; FStar_Syntax_Syntax.vars = uu____8831}, args) -> begin
(

let uu____8853 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____8853) with
| true -> begin
(

let uu____8854 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____8854) with
| ((FStar_Pervasives_Native.Some (true), uu____8909))::((uu____8910, (arg, uu____8912)))::[] -> begin
arg
end
| ((uu____8977, (arg, uu____8979)))::((FStar_Pervasives_Native.Some (true), uu____8980))::[] -> begin
arg
end
| ((FStar_Pervasives_Native.Some (false), uu____9045))::(uu____9046)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____9109)::((FStar_Pervasives_Native.Some (false), uu____9110))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____9173 -> begin
tm1
end))
end
| uu____9188 -> begin
(

let uu____9189 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____9189) with
| true -> begin
(

let uu____9190 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____9190) with
| ((FStar_Pervasives_Native.Some (true), uu____9245))::(uu____9246)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____9309)::((FStar_Pervasives_Native.Some (true), uu____9310))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____9373))::((uu____9374, (arg, uu____9376)))::[] -> begin
arg
end
| ((uu____9441, (arg, uu____9443)))::((FStar_Pervasives_Native.Some (false), uu____9444))::[] -> begin
arg
end
| uu____9509 -> begin
tm1
end))
end
| uu____9524 -> begin
(

let uu____9525 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____9525) with
| true -> begin
(

let uu____9526 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____9526) with
| (uu____9581)::((FStar_Pervasives_Native.Some (true), uu____9582))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____9645))::(uu____9646)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____9709))::((uu____9710, (arg, uu____9712)))::[] -> begin
arg
end
| ((uu____9777, (p, uu____9779)))::((uu____9780, (q, uu____9782)))::[] -> begin
(

let uu____9847 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____9847) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____9848 -> begin
tm1
end))
end
| uu____9849 -> begin
tm1
end))
end
| uu____9864 -> begin
(

let uu____9865 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____9865) with
| true -> begin
(

let uu____9866 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____9866) with
| ((FStar_Pervasives_Native.Some (true), uu____9921))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____9960))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____9999 -> begin
tm1
end))
end
| uu____10014 -> begin
(

let uu____10015 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____10015) with
| true -> begin
(match (args) with
| ((t, uu____10017))::[] -> begin
(

let uu____10034 = (

let uu____10035 = (FStar_Syntax_Subst.compress t)
in uu____10035.FStar_Syntax_Syntax.n)
in (match (uu____10034) with
| FStar_Syntax_Syntax.Tm_abs ((uu____10038)::[], body, uu____10040) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____10067 -> begin
tm1
end)
end
| uu____10070 -> begin
tm1
end))
end
| ((uu____10071, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10072))))::((t, uu____10074))::[] -> begin
(

let uu____10113 = (

let uu____10114 = (FStar_Syntax_Subst.compress t)
in uu____10114.FStar_Syntax_Syntax.n)
in (match (uu____10113) with
| FStar_Syntax_Syntax.Tm_abs ((uu____10117)::[], body, uu____10119) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____10146 -> begin
tm1
end)
end
| uu____10149 -> begin
tm1
end))
end
| uu____10150 -> begin
tm1
end)
end
| uu____10159 -> begin
(

let uu____10160 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____10160) with
| true -> begin
(match (args) with
| ((t, uu____10162))::[] -> begin
(

let uu____10179 = (

let uu____10180 = (FStar_Syntax_Subst.compress t)
in uu____10180.FStar_Syntax_Syntax.n)
in (match (uu____10179) with
| FStar_Syntax_Syntax.Tm_abs ((uu____10183)::[], body, uu____10185) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____10212 -> begin
tm1
end)
end
| uu____10215 -> begin
tm1
end))
end
| ((uu____10216, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10217))))::((t, uu____10219))::[] -> begin
(

let uu____10258 = (

let uu____10259 = (FStar_Syntax_Subst.compress t)
in uu____10259.FStar_Syntax_Syntax.n)
in (match (uu____10258) with
| FStar_Syntax_Syntax.Tm_abs ((uu____10262)::[], body, uu____10264) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____10291 -> begin
tm1
end)
end
| uu____10294 -> begin
tm1
end))
end
| uu____10295 -> begin
tm1
end)
end
| uu____10304 -> begin
(

let uu____10305 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
in (match (uu____10305) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____10306; FStar_Syntax_Syntax.vars = uu____10307}, uu____10308))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____10325; FStar_Syntax_Syntax.vars = uu____10326}, uu____10327))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____10344 -> begin
tm1
end)
end
| uu____10353 -> begin
(reduce_equality cfg env stack1 tm1)
end))
end))
end))
end))
end))
end))
end))
end
| uu____10354 -> begin
tm1
end))))
end))))


let is_norm_request : 'Auu____10361 . FStar_Syntax_Syntax.term  ->  'Auu____10361 Prims.list  ->  Prims.bool = (fun hd1 args -> (

let uu____10374 = (

let uu____10381 = (

let uu____10382 = (FStar_Syntax_Util.un_uinst hd1)
in uu____10382.FStar_Syntax_Syntax.n)
in ((uu____10381), (args)))
in (match (uu____10374) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____10388)::(uu____10389)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____10393)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (steps)::(uu____10398)::(uu____10399)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm)
end
| uu____10402 -> begin
false
end)))


let tr_norm_step : FStar_Syntax_Embeddings.norm_step  ->  step Prims.list = (fun uu___185_10414 -> (match (uu___185_10414) with
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

let uu____10420 = (

let uu____10423 = (

let uu____10424 = (FStar_List.map FStar_Ident.lid_of_str names1)
in UnfoldOnly (uu____10424))
in (uu____10423)::[])
in (UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::uu____10420)
end))


let tr_norm_steps : FStar_Syntax_Embeddings.norm_step Prims.list  ->  step Prims.list = (fun s -> (FStar_List.concatMap tr_norm_step s))


let get_norm_request : 'Auu____10443 . (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term * 'Auu____10443) Prims.list  ->  (step Prims.list * FStar_Syntax_Syntax.term) = (fun full_norm args -> (

let parse_steps = (fun s -> (

let uu____10481 = (

let uu____10484 = (

let uu____10489 = (FStar_Syntax_Embeddings.unembed_list FStar_Syntax_Embeddings.unembed_norm_step)
in (uu____10489 s))
in (FStar_All.pipe_right uu____10484 FStar_Util.must))
in (FStar_All.pipe_right uu____10481 tr_norm_steps)))
in (match (args) with
| (uu____10514)::((tm, uu____10516))::[] -> begin
(

let s = (Beta)::(Zeta)::(Iota)::(Primops)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Reify)::[]
in ((s), (tm)))
end
| ((tm, uu____10539))::[] -> begin
(

let s = (Beta)::(Zeta)::(Iota)::(Primops)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Reify)::[]
in ((s), (tm)))
end
| ((steps, uu____10554))::(uu____10555)::((tm, uu____10557))::[] -> begin
(

let add_exclude = (fun s z -> (match ((not ((FStar_List.contains z s)))) with
| true -> begin
(Exclude (z))::s
end
| uu____10593 -> begin
s
end))
in (

let s = (

let uu____10597 = (

let uu____10600 = (full_norm steps)
in (parse_steps uu____10600))
in (Beta)::uu____10597)
in (

let s1 = (add_exclude s Zeta)
in (

let s2 = (add_exclude s1 Iota)
in ((s2), (tm))))))
end
| uu____10609 -> begin
(failwith "Impossible")
end)))


let is_reify_head : stack_elt Prims.list  ->  Prims.bool = (fun uu___186_10627 -> (match (uu___186_10627) with
| (App (uu____10630, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____10631; FStar_Syntax_Syntax.vars = uu____10632}, uu____10633, uu____10634))::uu____10635 -> begin
true
end
| uu____10642 -> begin
false
end))


let firstn : 'Auu____10651 . Prims.int  ->  'Auu____10651 Prims.list  ->  ('Auu____10651 Prims.list * 'Auu____10651 Prims.list) = (fun k l -> (match (((FStar_List.length l) < k)) with
| true -> begin
((l), ([]))
end
| uu____10676 -> begin
(FStar_Util.first_N k l)
end))


let should_reify : cfg  ->  stack_elt Prims.list  ->  Prims.bool = (fun cfg stack1 -> (match (stack1) with
| (App (uu____10689, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____10690; FStar_Syntax_Syntax.vars = uu____10691}, uu____10692, uu____10693))::uu____10694 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____10701 -> begin
false
end))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in ((log cfg (fun uu____10817 -> (

let uu____10818 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____10819 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10820 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____10827 = (

let uu____10828 = (

let uu____10831 = (firstn (Prims.parse_int "4") stack1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10831))
in (stack_to_string uu____10828))
in (FStar_Util.print4 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n" uu____10818 uu____10819 uu____10820 uu____10827)))))));
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____10854) -> begin
(failwith "Impossible: got a delayed substitution")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____10879) when (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars)) -> begin
(

let uu____10896 = (

let uu____10897 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____10898 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s) CheckNoUvars: Unexpected unification variable remains: %s" uu____10897 uu____10898)))
in (failwith uu____10896))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____10899) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_constant (uu____10916) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____10917) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10918; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = uu____10919}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10922; FStar_Syntax_Syntax.fv_delta = uu____10923; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10924; FStar_Syntax_Syntax.fv_delta = uu____10925; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____10926))}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____10934 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_TypeChecker_Env.is_action cfg.tcenv uu____10934)) -> begin
(

let b = (should_reify cfg stack1)
in ((log cfg (fun uu____10940 -> (

let uu____10941 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10942 = (FStar_Util.string_of_bool b)
in (FStar_Util.print2 ">>> For DM4F action %s, should_reify = %s\n" uu____10941 uu____10942)))));
(match (b) with
| true -> begin
(

let uu____10943 = (FStar_List.tl stack1)
in (do_unfold_fv cfg env uu____10943 t1 fv))
end
| uu____10946 -> begin
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

let uu___222_10982 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd2), (args1))); FStar_Syntax_Syntax.pos = uu___222_10982.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___222_10982.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack1 t2))))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when (((

let uu____11015 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoFullNorm))
in (not (uu____11015))) && (is_norm_request hd1 args)) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid)))) -> begin
(

let cfg' = (

let uu___223_11023 = cfg
in (

let uu____11024 = (FStar_List.filter (fun uu___187_11027 -> (match (uu___187_11027) with
| UnfoldOnly (uu____11028) -> begin
false
end
| NoDeltaSteps -> begin
false
end
| uu____11031 -> begin
true
end)) cfg.steps)
in {steps = uu____11024; tcenv = uu___223_11023.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]; primitive_steps = uu___223_11023.primitive_steps}))
in (

let uu____11032 = (get_norm_request (norm cfg' env []) args)
in (match (uu____11032) with
| (s, tm) -> begin
(

let delta_level = (

let uu____11048 = (FStar_All.pipe_right s (FStar_Util.for_some (fun uu___188_11053 -> (match (uu___188_11053) with
| UnfoldUntil (uu____11054) -> begin
true
end
| UnfoldOnly (uu____11055) -> begin
true
end
| uu____11058 -> begin
false
end))))
in (match (uu____11048) with
| true -> begin
(FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]
end
| uu____11061 -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end))
in (

let cfg'1 = (

let uu___224_11063 = cfg
in {steps = s; tcenv = uu___224_11063.tcenv; delta_level = delta_level; primitive_steps = uu___224_11063.primitive_steps})
in (

let stack' = (

let tail1 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let uu____11074 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms")))
in (match (uu____11074) with
| true -> begin
(

let uu____11077 = (

let uu____11078 = (

let uu____11083 = (FStar_Util.now ())
in ((t1), (uu____11083)))
in Debug (uu____11078))
in (uu____11077)::tail1)
end
| uu____11084 -> begin
tail1
end)))
in (norm cfg'1 env stack' tm))))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____11085; FStar_Syntax_Syntax.vars = uu____11086}, (a1)::(a2)::rest) -> begin
(

let uu____11134 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____11134) with
| (hd1, uu____11150) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), ((a1)::[])))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (norm cfg env stack1 t2)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____11215)); FStar_Syntax_Syntax.pos = uu____11216; FStar_Syntax_Syntax.vars = uu____11217}, (a)::[]) when ((FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) && (is_reify_head stack1)) -> begin
(

let uu____11249 = (FStar_List.tl stack1)
in (norm cfg env uu____11249 (FStar_Pervasives_Native.fst a)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____11252; FStar_Syntax_Syntax.vars = uu____11253}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let uu____11285 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____11285) with
| (reify_head, uu____11301) -> begin
(

let a1 = (

let uu____11323 = (FStar_All.pipe_left FStar_Syntax_Util.unascribe (FStar_Pervasives_Native.fst a))
in (FStar_Syntax_Subst.compress uu____11323))
in (match (a1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____11326)); FStar_Syntax_Syntax.pos = uu____11327; FStar_Syntax_Syntax.vars = uu____11328}, (a2)::[]) -> begin
(norm cfg env stack1 (FStar_Pervasives_Native.fst a2))
end
| uu____11362 -> begin
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

let uu____11372 = (mk (FStar_Syntax_Syntax.Tm_type (u1)) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 uu____11372)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let uu____11379 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____11379) with
| true -> begin
(norm cfg env stack1 t')
end
| uu____11380 -> begin
(

let us1 = (

let uu____11382 = (

let uu____11389 = (FStar_List.map (norm_universe cfg env) us)
in ((uu____11389), (t1.FStar_Syntax_Syntax.pos)))
in UnivArgs (uu____11382))
in (

let stack2 = (us1)::stack1
in (norm cfg env stack2 t')))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun uu___189_11402 -> (match (uu___189_11402) with
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

let uu____11405 = ((FStar_List.mem FStar_TypeChecker_Env.UnfoldTac cfg.delta_level) && (((((((((FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.and_lid) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.imp_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.forall_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.exists_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.eq2_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.true_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.false_lid)))
in (match (uu____11405) with
| true -> begin
false
end
| uu____11406 -> begin
(

let uu____11407 = (FStar_All.pipe_right cfg.steps (FStar_List.tryFind (fun uu___190_11414 -> (match (uu___190_11414) with
| UnfoldOnly (uu____11415) -> begin
true
end
| uu____11418 -> begin
false
end))))
in (match (uu____11407) with
| FStar_Pervasives_Native.Some (UnfoldOnly (lids)) -> begin
(should_delta && (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid f) lids))
end
| uu____11422 -> begin
should_delta
end))
end))
in ((log cfg (fun uu____11430 -> (

let uu____11431 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____11432 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____11433 = (FStar_Util.string_of_bool should_delta1)
in (FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n" uu____11431 uu____11432 uu____11433))))));
(match ((not (should_delta1))) with
| true -> begin
(rebuild cfg env stack1 t1)
end
| uu____11434 -> begin
(do_unfold_fv cfg env stack1 t1 f)
end);
)))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____11436 = (lookup_bvar env x)
in (match (uu____11436) with
| Univ (uu____11439) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env1, t0, r, fix) -> begin
(match (((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps))))) with
| true -> begin
(

let uu____11488 = (FStar_ST.op_Bang r)
in (match (uu____11488) with
| FStar_Pervasives_Native.Some (env2, t') -> begin
((log cfg (fun uu____11625 -> (

let uu____11626 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____11627 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" uu____11626 uu____11627)))));
(

let uu____11628 = (

let uu____11629 = (FStar_Syntax_Subst.compress t')
in uu____11629.FStar_Syntax_Syntax.n)
in (match (uu____11628) with
| FStar_Syntax_Syntax.Tm_abs (uu____11632) -> begin
(norm cfg env2 stack1 t')
end
| uu____11649 -> begin
(rebuild cfg env2 stack1 t')
end));
)
end
| FStar_Pervasives_Native.None -> begin
(norm cfg env1 ((MemoLazy (r))::stack1) t0)
end))
end
| uu____11683 -> begin
(norm cfg env1 stack1 t0)
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack1) with
| (UnivArgs (uu____11707))::uu____11708 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (uu____11717))::uu____11718 -> begin
(failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, uu____11728, uu____11729))::stack_rest -> begin
(match (c) with
| Univ (uu____11733) -> begin
(norm cfg ((((FStar_Pervasives_Native.None), (c)))::env) stack_rest t1)
end
| uu____11742 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (b)::[] -> begin
((log cfg (fun uu____11763 -> (

let uu____11764 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____11764))));
(norm cfg ((((FStar_Pervasives_Native.Some (b)), (c)))::env) stack_rest body);
)
end
| (b)::tl1 -> begin
((log cfg (fun uu____11804 -> (

let uu____11805 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____11805))));
(

let body1 = (mk (FStar_Syntax_Syntax.Tm_abs (((tl1), (body), (lopt)))) t1.FStar_Syntax_Syntax.pos)
in (norm cfg ((((FStar_Pervasives_Native.Some (b)), (c)))::env) stack_rest body1));
)
end)
end)
end
| (Steps (s, ps, dl))::stack2 -> begin
(norm (

let uu___225_11855 = cfg
in {steps = s; tcenv = uu___225_11855.tcenv; delta_level = dl; primitive_steps = ps}) env stack2 t1)
end
| (MemoLazy (r))::stack2 -> begin
((set_memo r ((env), (t1)));
(log cfg (fun uu____11888 -> (

let uu____11889 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____11889))));
(norm cfg env stack2 t1);
)
end
| (Debug (uu____11890))::uu____11891 -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(

let uu____11898 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____11898))
end
| uu____11899 -> begin
(

let uu____11900 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11900) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11942 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____11970 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____11970) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11980 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11980))))
end
| uu____11981 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___226_11985 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___226_11985.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___226_11985.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11986 -> begin
lopt
end)
in ((log cfg (fun uu____11992 -> (

let uu____11993 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11993))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (only_strong_steps cfg)
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Meta (uu____12016))::uu____12017 -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(

let uu____12024 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12024))
end
| uu____12025 -> begin
(

let uu____12026 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____12026) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____12068 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____12096 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____12096) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____12106 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____12106))))
end
| uu____12107 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___226_12111 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___226_12111.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___226_12111.FStar_Syntax_Syntax.residual_flags})))
end
| uu____12112 -> begin
lopt
end)
in ((log cfg (fun uu____12118 -> (

let uu____12119 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____12119))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (only_strong_steps cfg)
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Let (uu____12142))::uu____12143 -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(

let uu____12154 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12154))
end
| uu____12155 -> begin
(

let uu____12156 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____12156) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____12198 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____12226 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____12226) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____12236 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____12236))))
end
| uu____12237 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___226_12241 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___226_12241.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___226_12241.FStar_Syntax_Syntax.residual_flags})))
end
| uu____12242 -> begin
lopt
end)
in ((log cfg (fun uu____12248 -> (

let uu____12249 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____12249))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (only_strong_steps cfg)
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (App (uu____12272))::uu____12273 -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(

let uu____12284 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12284))
end
| uu____12285 -> begin
(

let uu____12286 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____12286) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____12328 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____12356 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____12356) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____12366 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____12366))))
end
| uu____12367 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___226_12371 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___226_12371.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___226_12371.FStar_Syntax_Syntax.residual_flags})))
end
| uu____12372 -> begin
lopt
end)
in ((log cfg (fun uu____12378 -> (

let uu____12379 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____12379))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (only_strong_steps cfg)
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Abs (uu____12402))::uu____12403 -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(

let uu____12418 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12418))
end
| uu____12419 -> begin
(

let uu____12420 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____12420) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____12462 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____12490 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____12490) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____12500 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____12500))))
end
| uu____12501 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___226_12505 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___226_12505.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___226_12505.FStar_Syntax_Syntax.residual_flags})))
end
| uu____12506 -> begin
lopt
end)
in ((log cfg (fun uu____12512 -> (

let uu____12513 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____12513))));
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

let uu____12536 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12536))
end
| uu____12537 -> begin
(

let uu____12538 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____12538) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____12580 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____12608 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____12608) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____12618 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____12618))))
end
| uu____12619 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___226_12623 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___226_12623.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___226_12623.FStar_Syntax_Syntax.residual_flags})))
end
| uu____12624 -> begin
lopt
end)
in ((log cfg (fun uu____12630 -> (

let uu____12631 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____12631))));
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

let stack2 = (FStar_All.pipe_right stack1 (FStar_List.fold_right (fun uu____12692 stack2 -> (match (uu____12692) with
| (a, aq) -> begin
(

let uu____12704 = (

let uu____12705 = (

let uu____12712 = (

let uu____12713 = (

let uu____12744 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____12744), (false)))
in Clos (uu____12713))
in ((uu____12712), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____12705))
in (uu____12704)::stack2)
end)) args))
in ((log cfg (fun uu____12820 -> (

let uu____12821 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____12821))));
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

let uu___227_12857 = x
in {FStar_Syntax_Syntax.ppname = uu___227_12857.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___227_12857.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 t2)))
end
| uu____12858 -> begin
(

let uu____12863 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12863))
end)
end
| uu____12864 -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let uu____12866 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____12866) with
| (closing, f1) -> begin
(

let f2 = (norm cfg ((dummy)::env) [] f1)
in (

let t2 = (

let uu____12897 = (

let uu____12898 = (

let uu____12905 = (FStar_Syntax_Subst.close closing f2)
in (((

let uu___228_12907 = x
in {FStar_Syntax_Syntax.ppname = uu___228_12907.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___228_12907.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (uu____12905)))
in FStar_Syntax_Syntax.Tm_refine (uu____12898))
in (mk uu____12897 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack1 t2)))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((FStar_List.contains Weak cfg.steps)) with
| true -> begin
(

let uu____12926 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12926))
end
| uu____12927 -> begin
(

let uu____12928 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____12928) with
| (bs1, c1) -> begin
(

let c2 = (

let uu____12936 = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____12960 -> (dummy)::env1) env))
in (norm_comp cfg uu____12936 c1))
in (

let t2 = (

let uu____12982 = (norm_binders cfg env bs1)
in (FStar_Syntax_Util.arrow uu____12982 c2))
in (rebuild cfg env stack1 t2)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) -> begin
(match (stack1) with
| (Match (uu____13041))::uu____13042 -> begin
((log cfg (fun uu____13053 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack1 t11);
)
end
| (Arg (uu____13054))::uu____13055 -> begin
((log cfg (fun uu____13066 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack1 t11);
)
end
| (App (uu____13067, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____13068; FStar_Syntax_Syntax.vars = uu____13069}, uu____13070, uu____13071))::uu____13072 -> begin
((log cfg (fun uu____13081 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack1 t11);
)
end
| (MemoLazy (uu____13082))::uu____13083 -> begin
((log cfg (fun uu____13094 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack1 t11);
)
end
| uu____13095 -> begin
((log cfg (fun uu____13098 -> (FStar_Util.print_string "+++ Keeping ascription \n")));
(

let t12 = (norm cfg env [] t11)
in ((log cfg (fun uu____13102 -> (FStar_Util.print_string "+++ Normalizing ascription \n")));
(

let tc1 = (match (tc) with
| FStar_Util.Inl (t2) -> begin
(

let uu____13119 = (norm cfg env [] t2)
in FStar_Util.Inl (uu____13119))
end
| FStar_Util.Inr (c) -> begin
(

let uu____13127 = (norm_comp cfg env c)
in FStar_Util.Inr (uu____13127))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (norm cfg env []))
in (

let uu____13133 = (

let uu____13134 = (

let uu____13135 = (

let uu____13162 = (FStar_Syntax_Util.unascribe t12)
in ((uu____13162), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____13135))
in (mk uu____13134 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack1 uu____13133))));
));
)
end)
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let stack2 = (Match (((env), (branches), (t1.FStar_Syntax_Syntax.pos))))::stack1
in (norm cfg env stack2 head1))
end
| FStar_Syntax_Syntax.Tm_let ((uu____13238, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____13239); FStar_Syntax_Syntax.lbunivs = uu____13240; FStar_Syntax_Syntax.lbtyp = uu____13241; FStar_Syntax_Syntax.lbeff = uu____13242; FStar_Syntax_Syntax.lbdef = uu____13243})::uu____13244), uu____13245) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n1 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in (

let uu____13281 = ((

let uu____13284 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps))
in (not (uu____13284))) && ((FStar_Syntax_Util.is_pure_effect n1) || ((FStar_Syntax_Util.is_ghost_effect n1) && (

let uu____13286 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (not (uu____13286))))))
in (match (uu____13281) with
| true -> begin
(

let binder = (

let uu____13288 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____13288))
in (

let env1 = (

let uu____13298 = (

let uu____13305 = (

let uu____13306 = (

let uu____13337 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (uu____13337), (false)))
in Clos (uu____13306))
in ((FStar_Pervasives_Native.Some (binder)), (uu____13305)))
in (uu____13298)::env)
in ((log cfg (fun uu____13422 -> (FStar_Util.print_string "+++ Reducing Tm_let\n")));
(norm cfg env1 stack1 body);
)))
end
| uu____13423 -> begin
(

let uu____13424 = (

let uu____13429 = (

let uu____13430 = (

let uu____13431 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right uu____13431 FStar_Syntax_Syntax.mk_binder))
in (uu____13430)::[])
in (FStar_Syntax_Subst.open_term uu____13429 body))
in (match (uu____13424) with
| (bs, body1) -> begin
((log cfg (fun uu____13440 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- type\n")));
(

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let x = (

let uu____13448 = (FStar_List.hd bs)
in (FStar_Pervasives_Native.fst uu____13448))
in FStar_Util.Inl ((

let uu___229_13458 = x
in {FStar_Syntax_Syntax.ppname = uu___229_13458.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___229_13458.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
in ((log cfg (fun uu____13461 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- definiens\n")));
(

let lb1 = (

let uu___230_13463 = lb
in (

let uu____13464 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___230_13463.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___230_13463.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____13464}))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env1 uu____13499 -> (dummy)::env1) env))
in (

let cfg1 = (only_strong_steps cfg)
in ((log cfg1 (fun uu____13521 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- body\n")));
(norm cfg1 env' ((Let (((env), (bs), (lb1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1);
))));
)));
)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), body) when ((FStar_List.contains CompressUvars cfg.steps) || ((FStar_List.contains (Exclude (Zeta)) cfg.steps) && (FStar_List.contains PureSubtermsWithinComputations cfg.steps))) -> begin
(

let uu____13538 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____13538) with
| (lbs1, body1) -> begin
(

let lbs2 = (FStar_List.map (fun lb -> (

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let uu____13574 = (

let uu___231_13575 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___231_13575.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___231_13575.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})
in FStar_Util.Inl (uu____13574))
in (

let uu____13576 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____13576) with
| (xs, def_body, lopt) -> begin
(

let xs1 = (norm_binders cfg env xs)
in (

let env1 = (

let uu____13602 = (FStar_List.map (fun uu____13618 -> dummy) lbs1)
in (

let uu____13619 = (

let uu____13628 = (FStar_List.map (fun uu____13648 -> dummy) xs1)
in (FStar_List.append uu____13628 env))
in (FStar_List.append uu____13602 uu____13619)))
in (

let def_body1 = (norm cfg env1 [] def_body)
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____13672 = (

let uu___232_13673 = rc
in (

let uu____13674 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env1 []))
in {FStar_Syntax_Syntax.residual_effect = uu___232_13673.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____13674; FStar_Syntax_Syntax.residual_flags = uu___232_13673.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____13672))
end
| uu____13681 -> begin
lopt
end)
in (

let def = (FStar_Syntax_Util.abs xs1 def_body1 lopt1)
in (

let uu___233_13685 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___233_13685.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___233_13685.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def}))))))
end))))) lbs1)
in (

let env' = (

let uu____13695 = (FStar_List.map (fun uu____13711 -> dummy) lbs2)
in (FStar_List.append uu____13695 env))
in (

let body2 = (norm cfg env' [] body1)
in (

let uu____13719 = (FStar_Syntax_Subst.close_let_rec lbs2 body2)
in (match (uu____13719) with
| (lbs3, body3) -> begin
(

let t2 = (

let uu___234_13735 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (body3))); FStar_Syntax_Syntax.pos = uu___234_13735.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___234_13735.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack1 t2))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(

let uu____13762 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____13762))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let uu____13781 = (FStar_List.fold_right (fun lb uu____13857 -> (match (uu____13857) with
| (rec_env, memos, i) -> begin
(

let bv = (

let uu___235_13978 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___235_13978.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___235_13978.FStar_Syntax_Syntax.sort})
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
in (match (uu____13781) with
| (rec_env, memos, uu____14175) -> begin
(

let uu____14228 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (FStar_Pervasives_Native.Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (FStar_Pervasives_Native.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env1 -> (

let uu____14759 = (

let uu____14766 = (

let uu____14767 = (

let uu____14798 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (uu____14798), (false)))
in Clos (uu____14767))
in ((FStar_Pervasives_Native.None), (uu____14766)))
in (uu____14759)::env1)) (FStar_Pervasives_Native.snd lbs) env)
in (norm cfg body_env stack1 body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head1, m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m1, t2) -> begin
(

let uu____14903 = (

let uu____14904 = (should_reify cfg stack1)
in (not (uu____14904)))
in (match (uu____14903) with
| true -> begin
(

let t3 = (norm cfg env [] t2)
in (

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu____14914 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____14914) with
| true -> begin
(

let uu___236_14915 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::(NoDeltaSteps)::[]; tcenv = uu___236_14915.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___236_14915.primitive_steps})
end
| uu____14916 -> begin
(

let uu___237_14917 = cfg
in {steps = (FStar_List.append ((Exclude (Zeta))::[]) cfg.steps); tcenv = uu___237_14917.tcenv; delta_level = uu___237_14917.delta_level; primitive_steps = uu___237_14917.primitive_steps})
end))
in (norm cfg1 env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m1), (t3)))), (t3.FStar_Syntax_Syntax.pos))))::stack2) head1))))
end
| uu____14918 -> begin
(

let uu____14919 = (

let uu____14920 = (FStar_Syntax_Subst.compress head1)
in uu____14920.FStar_Syntax_Syntax.n)
in (match (uu____14919) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m1)
in (

let uu____14938 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____14938) with
| (uu____14939, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____14945) -> begin
(failwith "Cannot reify a top-level let binding")
end
| FStar_Util.Inl (x) -> begin
(

let is_return = (fun e -> (

let uu____14953 = (

let uu____14954 = (FStar_Syntax_Subst.compress e)
in uu____14954.FStar_Syntax_Syntax.n)
in (match (uu____14953) with
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____14960, uu____14961)) -> begin
(

let uu____14970 = (

let uu____14971 = (FStar_Syntax_Subst.compress e1)
in uu____14971.FStar_Syntax_Syntax.n)
in (match (uu____14970) with
| FStar_Syntax_Syntax.Tm_meta (e2, FStar_Syntax_Syntax.Meta_monadic_lift (uu____14977, msrc, uu____14979)) when (FStar_Syntax_Util.is_pure_effect msrc) -> begin
(

let uu____14988 = (FStar_Syntax_Subst.compress e2)
in FStar_Pervasives_Native.Some (uu____14988))
end
| uu____14989 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____14990 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____14991 = (is_return lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____14991) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let lb1 = (

let uu___238_14996 = lb
in {FStar_Syntax_Syntax.lbname = uu___238_14996.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___238_14996.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___238_14996.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = e})
in (

let uu____14997 = (FStar_List.tl stack1)
in (

let uu____14998 = (

let uu____14999 = (

let uu____15002 = (

let uu____15003 = (

let uu____15016 = (FStar_Syntax_Util.mk_reify body)
in ((((false), ((lb1)::[]))), (uu____15016)))
in FStar_Syntax_Syntax.Tm_let (uu____15003))
in (FStar_Syntax_Syntax.mk uu____15002))
in (uu____14999 FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos))
in (norm cfg env uu____14997 uu____14998))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____15032 = (

let uu____15033 = (is_return body)
in (match (uu____15033) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_bvar (y); FStar_Syntax_Syntax.pos = uu____15037; FStar_Syntax_Syntax.vars = uu____15038}) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____15043 -> begin
false
end))
in (match (uu____15032) with
| true -> begin
(norm cfg env stack1 lb.FStar_Syntax_Syntax.lbdef)
end
| uu____15046 -> begin
(

let head2 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body1 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify body)
in (

let body_rc = {FStar_Syntax_Syntax.residual_effect = m1; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t2); FStar_Syntax_Syntax.residual_flags = []}
in (

let body2 = (

let uu____15067 = (

let uu____15070 = (

let uu____15071 = (

let uu____15088 = (

let uu____15091 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____15091)::[])
in ((uu____15088), (body1), (FStar_Pervasives_Native.Some (body_rc))))
in FStar_Syntax_Syntax.Tm_abs (uu____15071))
in (FStar_Syntax_Syntax.mk uu____15070))
in (uu____15067 FStar_Pervasives_Native.None body1.FStar_Syntax_Syntax.pos))
in (

let close1 = (closure_as_term cfg env)
in (

let bind_inst = (

let uu____15107 = (

let uu____15108 = (FStar_Syntax_Subst.compress bind_repr)
in uu____15108.FStar_Syntax_Syntax.n)
in (match (uu____15107) with
| FStar_Syntax_Syntax.Tm_uinst (bind1, (uu____15114)::(uu____15115)::[]) -> begin
(

let uu____15122 = (

let uu____15125 = (

let uu____15126 = (

let uu____15133 = (

let uu____15136 = (

let uu____15137 = (close1 lb.FStar_Syntax_Syntax.lbtyp)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____15137))
in (

let uu____15138 = (

let uu____15141 = (

let uu____15142 = (close1 t2)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____15142))
in (uu____15141)::[])
in (uu____15136)::uu____15138))
in ((bind1), (uu____15133)))
in FStar_Syntax_Syntax.Tm_uinst (uu____15126))
in (FStar_Syntax_Syntax.mk uu____15125))
in (uu____15122 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
end
| uu____15150 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let reified = (

let uu____15156 = (

let uu____15159 = (

let uu____15160 = (

let uu____15175 = (

let uu____15178 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____15179 = (

let uu____15182 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____15183 = (

let uu____15186 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____15187 = (

let uu____15190 = (FStar_Syntax_Syntax.as_arg head2)
in (

let uu____15191 = (

let uu____15194 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____15195 = (

let uu____15198 = (FStar_Syntax_Syntax.as_arg body2)
in (uu____15198)::[])
in (uu____15194)::uu____15195))
in (uu____15190)::uu____15191))
in (uu____15186)::uu____15187))
in (uu____15182)::uu____15183))
in (uu____15178)::uu____15179))
in ((bind_inst), (uu____15175)))
in FStar_Syntax_Syntax.Tm_app (uu____15160))
in (FStar_Syntax_Syntax.mk uu____15159))
in (uu____15156 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (

let uu____15206 = (FStar_List.tl stack1)
in (norm cfg env uu____15206 reified)))))))))
end))
end)))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head_app, args) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m1)
in (

let uu____15230 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____15230) with
| (uu____15231, bind_repr) -> begin
(

let maybe_unfold_action = (fun head2 -> (

let maybe_extract_fv = (fun t3 -> (

let t4 = (

let uu____15266 = (

let uu____15267 = (FStar_Syntax_Subst.compress t3)
in uu____15267.FStar_Syntax_Syntax.n)
in (match (uu____15266) with
| FStar_Syntax_Syntax.Tm_uinst (t4, uu____15273) -> begin
t4
end
| uu____15278 -> begin
head2
end))
in (

let uu____15279 = (

let uu____15280 = (FStar_Syntax_Subst.compress t4)
in uu____15280.FStar_Syntax_Syntax.n)
in (match (uu____15279) with
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____15286 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____15287 = (maybe_extract_fv head2)
in (match (uu____15287) with
| FStar_Pervasives_Native.Some (x) when (

let uu____15297 = (FStar_Syntax_Syntax.lid_of_fv x)
in (FStar_TypeChecker_Env.is_action cfg.tcenv uu____15297)) -> begin
(

let head3 = (norm cfg env [] head2)
in (

let action_unfolded = (

let uu____15302 = (maybe_extract_fv head3)
in (match (uu____15302) with
| FStar_Pervasives_Native.Some (uu____15307) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____15308 -> begin
FStar_Pervasives_Native.Some (false)
end))
in ((head3), (action_unfolded))))
end
| uu____15313 -> begin
((head2), (FStar_Pervasives_Native.None))
end))))
in ((

let is_arg_impure = (fun uu____15328 -> (match (uu____15328) with
| (e, q) -> begin
(

let uu____15335 = (

let uu____15336 = (FStar_Syntax_Subst.compress e)
in uu____15336.FStar_Syntax_Syntax.n)
in (match (uu____15335) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m11, m2, t')) -> begin
(not ((FStar_Syntax_Util.is_pure_effect m11)))
end
| uu____15351 -> begin
false
end))
end))
in (

let uu____15352 = (

let uu____15353 = (

let uu____15360 = (FStar_Syntax_Syntax.as_arg head_app)
in (uu____15360)::args)
in (FStar_Util.for_some is_arg_impure uu____15353))
in (match (uu____15352) with
| true -> begin
(

let uu____15365 = (

let uu____15366 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format1 "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n" uu____15366))
in (failwith uu____15365))
end
| uu____15367 -> begin
()
end)));
(

let uu____15368 = (maybe_unfold_action head_app)
in (match (uu____15368) with
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

let uu____15407 = (FStar_List.tl stack1)
in (norm cfg env uu____15407 body1)))))
end));
))
end)))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (

let uu____15421 = (closure_as_term cfg env t')
in (reify_lift cfg.tcenv e msrc mtgt uu____15421))
in (

let uu____15422 = (FStar_List.tl stack1)
in (norm cfg env uu____15422 lifted)))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____15543 -> (match (uu____15543) with
| (pat, wopt, tm) -> begin
(

let uu____15591 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____15591)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches1)))) t2.FStar_Syntax_Syntax.pos)
in (

let uu____15623 = (FStar_List.tl stack1)
in (norm cfg env uu____15623 tm))))
end
| uu____15624 -> begin
(norm cfg env stack1 head1)
end))
end))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) -> begin
(

let uu____15632 = (should_reify cfg stack1)
in (match (uu____15632) with
| true -> begin
(

let uu____15633 = (FStar_List.tl stack1)
in (

let uu____15634 = (

let uu____15635 = (closure_as_term cfg env t2)
in (reify_lift cfg.tcenv head1 m1 m' uu____15635))
in (norm cfg env uu____15633 uu____15634)))
end
| uu____15636 -> begin
(

let t3 = (norm cfg env [] t2)
in (

let uu____15638 = (((FStar_Syntax_Util.is_pure_effect m1) || (FStar_Syntax_Util.is_ghost_effect m1)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)))
in (match (uu____15638) with
| true -> begin
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___239_15647 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = uu___239_15647.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___239_15647.primitive_steps})
in (norm cfg1 env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t3)))), (head1.FStar_Syntax_Syntax.pos))))::stack2) head1)))
end
| uu____15648 -> begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t3)))), (head1.FStar_Syntax_Syntax.pos))))::stack1) head1)
end)))
end))
end
| uu____15649 -> begin
(match ((FStar_List.contains Unmeta cfg.steps)) with
| true -> begin
(norm cfg env stack1 head1)
end
| uu____15650 -> begin
(match (stack1) with
| (uu____15651)::uu____15652 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____15657) -> begin
(norm cfg env ((Meta (((m), (r))))::stack1) head1)
end
| FStar_Syntax_Syntax.Meta_alien (uu____15658) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args1 = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args1)), (t1.FStar_Syntax_Syntax.pos))))::stack1) head1))
end
| uu____15689 -> begin
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

let uu____15703 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (uu____15703))
end
| uu____15714 -> begin
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

let uu____15726 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv uu____15726))
in (

let uu____15727 = (FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____15727) with
| FStar_Pervasives_Native.None -> begin
((log cfg (fun uu____15740 -> (FStar_Util.print "Tm_fvar case 2\n" [])));
(rebuild cfg env stack1 t0);
)
end
| FStar_Pervasives_Native.Some (us, t) -> begin
((log cfg (fun uu____15751 -> (

let uu____15752 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____15753 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15752 uu____15753)))));
(

let t1 = (

let uu____15755 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))))
in (match (uu____15755) with
| true -> begin
t
end
| uu____15756 -> begin
(FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) t)
end))
in (

let n1 = (FStar_List.length us)
in (match ((n1 > (Prims.parse_int "0"))) with
| true -> begin
(match (stack1) with
| (UnivArgs (us', uu____15765))::stack2 -> begin
(

let env1 = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env1 u -> (((FStar_Pervasives_Native.None), (Univ (u))))::env1) env))
in (norm cfg env1 stack2 t1))
end
| uu____15820 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack1 t1)
end
| uu____15823 -> begin
(

let uu____15826 = (

let uu____15827 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" uu____15827))
in (failwith uu____15826))
end)
end
| uu____15828 -> begin
(norm cfg env stack1 t1)
end)));
)
end))))
and reify_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env e msrc mtgt t -> (match ((FStar_Syntax_Util.is_pure_effect msrc)) with
| true -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl env mtgt)
in (

let uu____15837 = ed.FStar_Syntax_Syntax.return_repr
in (match (uu____15837) with
| (uu____15838, return_repr) -> begin
(

let return_inst = (

let uu____15847 = (

let uu____15848 = (FStar_Syntax_Subst.compress return_repr)
in uu____15848.FStar_Syntax_Syntax.n)
in (match (uu____15847) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (uu____15854)::[]) -> begin
(

let uu____15861 = (

let uu____15864 = (

let uu____15865 = (

let uu____15872 = (

let uu____15875 = (env.FStar_TypeChecker_Env.universe_of env t)
in (uu____15875)::[])
in ((return_tm), (uu____15872)))
in FStar_Syntax_Syntax.Tm_uinst (uu____15865))
in (FStar_Syntax_Syntax.mk uu____15864))
in (uu____15861 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end
| uu____15883 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let uu____15886 = (

let uu____15889 = (

let uu____15890 = (

let uu____15905 = (

let uu____15908 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____15909 = (

let uu____15912 = (FStar_Syntax_Syntax.as_arg e)
in (uu____15912)::[])
in (uu____15908)::uu____15909))
in ((return_inst), (uu____15905)))
in FStar_Syntax_Syntax.Tm_app (uu____15890))
in (FStar_Syntax_Syntax.mk uu____15889))
in (uu____15886 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end)))
end
| uu____15920 -> begin
(

let uu____15921 = (FStar_TypeChecker_Env.monad_leq env msrc mtgt)
in (match (uu____15921) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15924 = (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" (FStar_Ident.text_of_lid msrc) (FStar_Ident.text_of_lid mtgt))
in (failwith uu____15924))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____15925; FStar_TypeChecker_Env.mtarget = uu____15926; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____15927; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(failwith "Impossible : trying to reify a non-reifiable lift (from %s to %s)")
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____15938; FStar_TypeChecker_Env.mtarget = uu____15939; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____15940; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let uu____15958 = (FStar_Syntax_Util.mk_reify e)
in (lift t FStar_Syntax_Syntax.tun uu____15958))
end))
end))
and norm_pattern_args : cfg  ->  env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun uu____16014 -> (match (uu____16014) with
| (a, imp) -> begin
(

let uu____16025 = (norm cfg env [] a)
in ((uu____16025), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp1 = (ghost_to_pure_aux cfg env comp)
in (match (comp1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu___240_16042 = comp1
in (

let uu____16045 = (

let uu____16046 = (

let uu____16055 = (norm cfg env [] t)
in (

let uu____16056 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____16055), (uu____16056))))
in FStar_Syntax_Syntax.Total (uu____16046))
in {FStar_Syntax_Syntax.n = uu____16045; FStar_Syntax_Syntax.pos = uu___240_16042.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___240_16042.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu___241_16071 = comp1
in (

let uu____16074 = (

let uu____16075 = (

let uu____16084 = (norm cfg env [] t)
in (

let uu____16085 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____16084), (uu____16085))))
in FStar_Syntax_Syntax.GTotal (uu____16075))
in {FStar_Syntax_Syntax.n = uu____16074; FStar_Syntax_Syntax.pos = uu___241_16071.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___241_16071.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____16137 -> (match (uu____16137) with
| (a, i) -> begin
(

let uu____16148 = (norm cfg env [] a)
in ((uu____16148), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___191_16159 -> (match (uu___191_16159) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____16163 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____16163))
end
| f -> begin
f
end))))
in (

let uu___242_16167 = comp1
in (

let uu____16170 = (

let uu____16171 = (

let uu___243_16172 = ct
in (

let uu____16173 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (

let uu____16174 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____16177 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = uu____16173; FStar_Syntax_Syntax.effect_name = uu___243_16172.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____16174; FStar_Syntax_Syntax.effect_args = uu____16177; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (uu____16171))
in {FStar_Syntax_Syntax.n = uu____16170; FStar_Syntax_Syntax.pos = uu___242_16167.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___242_16167.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm1 = (fun t -> (norm (

let uu___244_16195 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = uu___244_16195.tcenv; delta_level = uu___244_16195.delta_level; primitive_steps = uu___244_16195.primitive_steps}) env [] t))
in (

let non_info = (fun t -> (

let uu____16200 = (norm1 t)
in (FStar_Syntax_Util.non_informative uu____16200)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____16203) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let uu___245_16222 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.pos = uu___245_16222.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___245_16222.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____16229 = ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ))
in (match (uu____16229) with
| true -> begin
(

let ct1 = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let flags = (match ((FStar_Ident.lid_equals pure_eff FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::ct.FStar_Syntax_Syntax.flags
end
| uu____16239 -> begin
ct.FStar_Syntax_Syntax.flags
end)
in (

let uu___246_16240 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___246_16240.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = uu___246_16240.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___246_16240.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags}))
end
| FStar_Pervasives_Native.None -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c)
in (

let uu___247_16242 = ct1
in {FStar_Syntax_Syntax.comp_univs = uu___247_16242.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu___247_16242.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___247_16242.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___247_16242.FStar_Syntax_Syntax.flags}))
end)
in (

let uu___248_16243 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___248_16243.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___248_16243.FStar_Syntax_Syntax.vars}))
end
| uu____16244 -> begin
c
end)))
end
| uu____16245 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env uu____16248 -> (match (uu____16248) with
| (x, imp) -> begin
(

let uu____16251 = (

let uu___249_16252 = x
in (

let uu____16253 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___249_16252.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___249_16252.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____16253}))
in ((uu____16251), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let uu____16259 = (FStar_List.fold_left (fun uu____16277 b -> (match (uu____16277) with
| (nbs', env1) -> begin
(

let b1 = (norm_binder cfg env1 b)
in (((b1)::nbs'), ((dummy)::env1)))
end)) (([]), (env)) bs)
in (match (uu____16259) with
| (nbs, uu____16317) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags = (filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags)
in (

let uu____16333 = (

let uu___250_16334 = rc
in (

let uu____16335 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___250_16334.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____16335; FStar_Syntax_Syntax.residual_flags = uu___250_16334.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____16333)))
end
| uu____16342 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 t -> ((log cfg (fun uu____16355 -> (

let uu____16356 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____16357 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____16358 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____16365 = (

let uu____16366 = (

let uu____16369 = (firstn (Prims.parse_int "4") stack1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____16369))
in (stack_to_string uu____16366))
in (FStar_Util.print4 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n" uu____16356 uu____16357 uu____16358 uu____16365)))))));
(match (stack1) with
| [] -> begin
t
end
| (Debug (tm, time_then))::stack2 -> begin
((

let uu____16398 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms")))
in (match (uu____16398) with
| true -> begin
(

let time_now = (FStar_Util.now ())
in (

let uu____16400 = (

let uu____16401 = (

let uu____16402 = (FStar_Util.time_diff time_then time_now)
in (FStar_Pervasives_Native.snd uu____16402))
in (FStar_Util.string_of_int uu____16401))
in (

let uu____16407 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____16408 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n" uu____16400 uu____16407 uu____16408)))))
end
| uu____16409 -> begin
()
end));
(rebuild cfg env stack2 t);
)
end
| (Steps (s, ps, dl))::stack2 -> begin
(rebuild (

let uu___251_16426 = cfg
in {steps = s; tcenv = uu___251_16426.tcenv; delta_level = dl; primitive_steps = ps}) env stack2 t)
end
| (Meta (m, r))::stack2 -> begin
(

let t1 = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack2 t1))
end
| (MemoLazy (r))::stack2 -> begin
((set_memo r ((env), (t)));
(log cfg (fun uu____16467 -> (

let uu____16468 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" uu____16468))));
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

let uu____16504 = (

let uu___252_16505 = (FStar_Syntax_Util.abs bs1 t lopt1)
in {FStar_Syntax_Syntax.n = uu___252_16505.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___252_16505.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack2 uu____16504))))
end
| (Arg (Univ (uu____16506), uu____16507, uu____16508))::uu____16509 -> begin
(failwith "Impossible")
end
| (Arg (Dummy, uu____16512, uu____16513))::uu____16514 -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack2 -> begin
(

let t1 = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack2 t1))
end
| (Arg (Clos (env_arg, tm, m, uu____16530), aq, r))::stack2 -> begin
((log cfg (fun uu____16583 -> (

let uu____16584 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" uu____16584))));
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
| uu____16589 -> begin
(

let stack3 = (App (((env), (t), (aq), (r))))::stack2
in (norm cfg env_arg stack3 tm))
end)
end
| uu____16593 -> begin
(

let uu____16594 = (FStar_ST.op_Bang m)
in (match (uu____16594) with
| FStar_Pervasives_Native.None -> begin
(match ((FStar_List.contains HNF cfg.steps)) with
| true -> begin
(

let arg = (closure_as_term cfg env_arg tm)
in (

let t1 = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack2 t1)))
end
| uu____16713 -> begin
(

let stack3 = (MemoLazy (m))::(App (((env), (t), (aq), (r))))::stack2
in (norm cfg env_arg stack3 tm))
end)
end
| FStar_Pervasives_Native.Some (uu____16738, a) -> begin
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

let uu____16781 = (maybe_simplify cfg env1 stack2 t1)
in (rebuild cfg env1 stack2 uu____16781)))
end
| (Match (env1, branches, r))::stack2 -> begin
((log cfg (fun uu____16793 -> (

let uu____16794 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" uu____16794))));
(

let scrutinee = t
in (

let norm_and_rebuild_match = (fun uu____16799 -> ((log cfg (fun uu____16804 -> (

let uu____16805 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____16806 = (

let uu____16807 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____16824 -> (match (uu____16824) with
| (p, uu____16834, uu____16835) -> begin
(FStar_Syntax_Print.pat_to_string p)
end))))
in (FStar_All.pipe_right uu____16807 (FStar_String.concat "\n\t")))
in (FStar_Util.print2 "match is irreducible: scrutinee=%s\nbranches=%s\n" uu____16805 uu____16806)))));
(

let whnf = ((FStar_List.contains Weak cfg.steps) || (FStar_List.contains HNF cfg.steps))
in (

let cfg_exclude_iota_zeta = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun uu___192_16852 -> (match (uu___192_16852) with
| FStar_TypeChecker_Env.Inlining -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| uu____16853 -> begin
false
end))))
in (

let steps' = (

let uu____16857 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____16857) with
| true -> begin
(Exclude (Zeta))::[]
end
| uu____16860 -> begin
(Exclude (Iota))::(Exclude (Zeta))::[]
end))
in (only_strong_steps (

let uu___253_16863 = cfg
in {steps = (FStar_List.append steps' cfg.steps); tcenv = uu___253_16863.tcenv; delta_level = new_delta; primitive_steps = uu___253_16863.primitive_steps}))))
in (

let norm_or_whnf = (fun env2 t1 -> (match (whnf) with
| true -> begin
(closure_as_term cfg_exclude_iota_zeta env2 t1)
end
| uu____16871 -> begin
(norm cfg_exclude_iota_zeta env2 [] t1)
end))
in (

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____16895) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____16916 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____16976 uu____16977 -> (match (((uu____16976), (uu____16977))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____17068 = (norm_pat env3 p1)
in (match (uu____17068) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____16916) with
| (pats1, env3) -> begin
(((

let uu___254_17150 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___254_17150.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___255_17169 = x
in (

let uu____17170 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___255_17169.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___255_17169.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____17170}))
in (((

let uu___256_17184 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___256_17184.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___257_17195 = x
in (

let uu____17196 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___257_17195.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___257_17195.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____17196}))
in (((

let uu___258_17210 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___258_17210.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t1) -> begin
(

let x1 = (

let uu___259_17226 = x
in (

let uu____17227 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___259_17226.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___259_17226.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____17227}))
in (

let t2 = (norm_or_whnf env2 t1)
in (((

let uu___260_17234 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t2))); FStar_Syntax_Syntax.p = uu___260_17234.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let branches1 = (match (env1) with
| [] when whnf -> begin
branches
end
| uu____17244 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch1 -> (

let uu____17258 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____17258) with
| (p, wopt, e) -> begin
(

let uu____17278 = (norm_pat env1 p)
in (match (uu____17278) with
| (p1, env2) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____17303 = (norm_or_whnf env2 w)
in FStar_Pervasives_Native.Some (uu____17303))
end)
in (

let e1 = (norm_or_whnf env2 e)
in (FStar_Syntax_Util.branch ((p1), (wopt1), (e1)))))
end))
end)))))
end)
in (

let uu____17309 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches1)))) r)
in (rebuild cfg env1 stack2 uu____17309)))))));
))
in (

let rec is_cons = (fun head1 -> (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, uu____17319) -> begin
(is_cons h)
end
| FStar_Syntax_Syntax.Tm_constant (uu____17324) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____17325; FStar_Syntax_Syntax.fv_delta = uu____17326; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____17327; FStar_Syntax_Syntax.fv_delta = uu____17328; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____17329))}) -> begin
true
end
| uu____17336 -> begin
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

let uu____17481 = (FStar_Syntax_Util.head_and_args scrutinee1)
in (match (uu____17481) with
| (head1, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____17568) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (Prims.op_Equality s s') -> begin
FStar_Util.Inl ([])
end
| uu____17607 -> begin
(

let uu____17608 = (

let uu____17609 = (is_cons head1)
in (not (uu____17609)))
in FStar_Util.Inr (uu____17608))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let uu____17634 = (

let uu____17635 = (FStar_Syntax_Util.un_uinst head1)
in uu____17635.FStar_Syntax_Syntax.n)
in (match (uu____17634) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| uu____17653 -> begin
(

let uu____17654 = (

let uu____17655 = (is_cons head1)
in (not (uu____17655)))
in FStar_Util.Inr (uu____17654))
end))
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t1, uu____17724))::rest_a, ((p1, uu____17727))::rest_p) -> begin
(

let uu____17771 = (matches_pat t1 p1)
in (match (uu____17771) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____17820 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee1 p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p1, wopt, b))::rest -> begin
(

let uu____17926 = (matches_pat scrutinee1 p1)
in (match (uu____17926) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee1 rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
((log cfg (fun uu____17966 -> (

let uu____17967 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____17968 = (

let uu____17969 = (FStar_List.map (fun uu____17979 -> (match (uu____17979) with
| (uu____17984, t1) -> begin
(FStar_Syntax_Print.term_to_string t1)
end)) s)
in (FStar_All.pipe_right uu____17969 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" uu____17967 uu____17968)))));
(

let env2 = (FStar_List.fold_left (fun env2 uu____18015 -> (match (uu____18015) with
| (bv, t1) -> begin
(

let uu____18038 = (

let uu____18045 = (

let uu____18048 = (FStar_Syntax_Syntax.mk_binder bv)
in FStar_Pervasives_Native.Some (uu____18048))
in (

let uu____18049 = (

let uu____18050 = (

let uu____18081 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ((([]), (t1)))))
in (([]), (t1), (uu____18081), (false)))
in Clos (uu____18050))
in ((uu____18045), (uu____18049))))
in (uu____18038)::env2)
end)) env1 s)
in (

let uu____18190 = (guard_when_clause wopt b rest)
in (norm cfg env2 stack2 uu____18190)));
)
end))
end))
in (

let uu____18191 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota))))
in (match (uu____18191) with
| true -> begin
(norm_and_rebuild_match ())
end
| uu____18192 -> begin
(matches scrutinee branches)
end))))))));
)
end);
))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun uu___193_18214 -> (match (uu___193_18214) with
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
| uu____18218 -> begin
[]
end))))
in (

let d1 = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| uu____18224 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d1; primitive_steps = built_in_primitive_steps})))


let normalize_with_primitive_steps : primitive_step Prims.list  ->  step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun ps s e t -> (

let c = (config s e)
in (

let c1 = (

let uu___261_18253 = (config s e)
in {steps = uu___261_18253.steps; tcenv = uu___261_18253.tcenv; delta_level = uu___261_18253.delta_level; primitive_steps = (FStar_List.append c.primitive_steps ps)})
in (norm c1 [] [] t))))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (normalize_with_primitive_steps [] s e t))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (

let uu____18284 = (config s e)
in (norm_comp uu____18284 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let uu____18299 = (config [] env)
in (norm_universe uu____18299 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (

let uu____18314 = (config [] env)
in (ghost_to_pure_aux uu____18314 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (

let uu____18334 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____18334)))
in (

let uu____18341 = ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ))
in (match (uu____18341) with
| true -> begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let uu___262_18343 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = uu___262_18343.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___262_18343.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____18346 -> (

let uu____18347 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env uu____18347)))})
end
| FStar_Pervasives_Native.None -> begin
lc
end)
end
| uu____18348 -> begin
lc
end)))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (

let t1 = (FStar_All.try_with (fun uu___264_18359 -> (match (()) with
| () -> begin
(normalize ((AllowUnboundUniverses)::[]) env t)
end)) (fun uu___263_18363 -> (match (uu___263_18363) with
| e -> begin
((

let uu____18366 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_warning "Normalization failed with error %s\n" uu____18366));
t;
)
end)))
in (FStar_Syntax_Print.term_to_string t1)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let c1 = (FStar_All.try_with (fun uu___266_18378 -> (match (()) with
| () -> begin
(

let uu____18379 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp uu____18379 [] c))
end)) (fun uu___265_18389 -> (match (uu___265_18389) with
| e -> begin
((

let uu____18392 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_warning "Normalization failed with error %s\n" uu____18392));
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

let uu____18432 = (

let uu____18433 = (

let uu____18440 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (uu____18440)))
in FStar_Syntax_Syntax.Tm_refine (uu____18433))
in (mk uu____18432 t01.FStar_Syntax_Syntax.pos))
end
| uu____18445 -> begin
t2
end))
end
| uu____18446 -> begin
t2
end)))
in (aux t))))


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((Weak)::(HNF)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Beta)::[]) env t))


let reduce_or_remove_uvar_solutions : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun remove env t -> (normalize (FStar_List.append (match (remove) with
| true -> begin
(CheckNoUvars)::[]
end
| uu____18469 -> begin
[]
end) ((Beta)::(NoDeltaSteps)::(CompressUvars)::(Exclude (Zeta))::(Exclude (Iota))::(NoFullNorm)::[])) env t))


let reduce_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions false env t))


let remove_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions true env t))


let eta_expand_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e t_e -> (

let uu____18498 = (FStar_Syntax_Util.arrow_formals_comp t_e)
in (match (uu____18498) with
| (formals, c) -> begin
(match (formals) with
| [] -> begin
e
end
| uu____18527 -> begin
(

let uu____18534 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____18534) with
| (actuals, uu____18544, uu____18545) -> begin
(match ((Prims.op_Equality (FStar_List.length actuals) (FStar_List.length formals))) with
| true -> begin
e
end
| uu____18558 -> begin
(

let uu____18559 = (FStar_All.pipe_right formals FStar_Syntax_Util.args_of_binders)
in (match (uu____18559) with
| (binders, args) -> begin
(

let uu____18576 = (FStar_Syntax_Syntax.mk_Tm_app e args FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Util.abs binders uu____18576 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c)))))
end))
end)
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(eta_expand_with_type env t x.FStar_Syntax_Syntax.sort)
end
| uu____18586 -> begin
(

let uu____18587 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____18587) with
| (head1, args) -> begin
(

let uu____18624 = (

let uu____18625 = (FStar_Syntax_Subst.compress head1)
in uu____18625.FStar_Syntax_Syntax.n)
in (match (uu____18624) with
| FStar_Syntax_Syntax.Tm_uvar (uu____18628, thead) -> begin
(

let uu____18654 = (FStar_Syntax_Util.arrow_formals thead)
in (match (uu____18654) with
| (formals, tres) -> begin
(match ((Prims.op_Equality (FStar_List.length formals) (FStar_List.length args))) with
| true -> begin
t
end
| uu____18695 -> begin
(

let uu____18696 = (env.FStar_TypeChecker_Env.type_of (

let uu___267_18704 = env
in {FStar_TypeChecker_Env.solver = uu___267_18704.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___267_18704.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___267_18704.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___267_18704.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___267_18704.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___267_18704.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___267_18704.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___267_18704.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___267_18704.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___267_18704.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___267_18704.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___267_18704.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___267_18704.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___267_18704.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___267_18704.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___267_18704.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___267_18704.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___267_18704.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___267_18704.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___267_18704.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___267_18704.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___267_18704.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___267_18704.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___267_18704.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___267_18704.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___267_18704.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___267_18704.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___267_18704.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___267_18704.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___267_18704.FStar_TypeChecker_Env.dsenv}) t)
in (match (uu____18696) with
| (uu____18705, ty, uu____18707) -> begin
(eta_expand_with_type env t ty)
end))
end)
end))
end
| uu____18708 -> begin
(

let uu____18709 = (env.FStar_TypeChecker_Env.type_of (

let uu___268_18717 = env
in {FStar_TypeChecker_Env.solver = uu___268_18717.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___268_18717.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___268_18717.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___268_18717.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___268_18717.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___268_18717.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___268_18717.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___268_18717.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___268_18717.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___268_18717.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___268_18717.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___268_18717.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___268_18717.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___268_18717.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___268_18717.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___268_18717.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___268_18717.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___268_18717.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___268_18717.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___268_18717.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___268_18717.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___268_18717.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___268_18717.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___268_18717.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___268_18717.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___268_18717.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___268_18717.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___268_18717.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___268_18717.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___268_18717.FStar_TypeChecker_Env.dsenv}) t)
in (match (uu____18709) with
| (uu____18718, ty, uu____18720) -> begin
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
| (uu____18798, FStar_Util.Inr (c)) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
end
| (uu____18804, FStar_Util.Inl (t)) -> begin
(

let uu____18810 = (

let uu____18813 = (

let uu____18814 = (

let uu____18827 = (FStar_Syntax_Syntax.mk_Total t)
in ((binders), (uu____18827)))
in FStar_Syntax_Syntax.Tm_arrow (uu____18814))
in (FStar_Syntax_Syntax.mk uu____18813))
in (uu____18810 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end)
in (

let uu____18831 = (FStar_Syntax_Subst.open_univ_vars univ_names t)
in (match (uu____18831) with
| (univ_names1, t1) -> begin
(

let t2 = (remove_uvar_solutions env t1)
in (

let t3 = (FStar_Syntax_Subst.close_univ_vars univ_names1 t2)
in (

let uu____18858 = (match (binders) with
| [] -> begin
(([]), (FStar_Util.Inl (t3)))
end
| uu____18913 -> begin
(

let uu____18914 = (

let uu____18923 = (

let uu____18924 = (FStar_Syntax_Subst.compress t3)
in uu____18924.FStar_Syntax_Syntax.n)
in ((uu____18923), (tc)))
in (match (uu____18914) with
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inr (uu____18949)) -> begin
((binders1), (FStar_Util.Inr (c)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inl (uu____18986)) -> begin
((binders1), (FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))))
end
| (uu____19025, FStar_Util.Inl (uu____19026)) -> begin
(([]), (FStar_Util.Inl (t3)))
end
| uu____19049 -> begin
(failwith "Impossible")
end))
end)
in (match (uu____18858) with
| (binders1, tc1) -> begin
((univ_names1), (binders1), (tc1))
end))))
end))))


let elim_uvars_aux_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term) = (fun env univ_names binders t -> (

let uu____19158 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl (t)))
in (match (uu____19158) with
| (univ_names1, binders1, tc) -> begin
(

let uu____19216 = (FStar_Util.left tc)
in ((univ_names1), (binders1), (uu____19216)))
end)))


let elim_uvars_aux_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) = (fun env univ_names binders c -> (

let uu____19255 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr (c)))
in (match (uu____19255) with
| (univ_names1, binders1, tc) -> begin
(

let uu____19315 = (FStar_Util.right tc)
in ((univ_names1), (binders1), (uu____19315)))
end)))


let rec elim_uvars : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, lids, lids') -> begin
(

let uu____19350 = (elim_uvars_aux_t env univ_names binders typ)
in (match (uu____19350) with
| (univ_names1, binders1, typ1) -> begin
(

let uu___269_19378 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univ_names1), (binders1), (typ1), (lids), (lids'))); FStar_Syntax_Syntax.sigrng = uu___269_19378.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___269_19378.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___269_19378.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___269_19378.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uu___270_19399 = s
in (

let uu____19400 = (

let uu____19401 = (

let uu____19410 = (FStar_List.map (elim_uvars env) sigs)
in ((uu____19410), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____19401))
in {FStar_Syntax_Syntax.sigel = uu____19400; FStar_Syntax_Syntax.sigrng = uu___270_19399.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___270_19399.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___270_19399.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___270_19399.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univ_names, typ, lident, i, lids) -> begin
(

let uu____19427 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____19427) with
| (univ_names1, uu____19445, typ1) -> begin
(

let uu___271_19459 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univ_names1), (typ1), (lident), (i), (lids))); FStar_Syntax_Syntax.sigrng = uu___271_19459.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___271_19459.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___271_19459.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___271_19459.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) -> begin
(

let uu____19465 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____19465) with
| (univ_names1, uu____19483, typ1) -> begin
(

let uu___272_19497 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (univ_names1), (typ1))); FStar_Syntax_Syntax.sigrng = uu___272_19497.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___272_19497.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___272_19497.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___272_19497.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____19531 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____19531) with
| (opening, lbunivs) -> begin
(

let elim = (fun t -> (

let uu____19554 = (

let uu____19555 = (FStar_Syntax_Subst.subst opening t)
in (remove_uvar_solutions env uu____19555))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____19554)))
in (

let lbtyp = (elim lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (elim lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___273_19558 = lb
in {FStar_Syntax_Syntax.lbname = uu___273_19558.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___273_19558.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}))))
end)))))
in (

let uu___274_19559 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((b), (lbs1))), (lids))); FStar_Syntax_Syntax.sigrng = uu___274_19559.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___274_19559.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___274_19559.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___274_19559.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(

let uu___275_19571 = s
in (

let uu____19572 = (

let uu____19573 = (remove_uvar_solutions env t)
in FStar_Syntax_Syntax.Sig_main (uu____19573))
in {FStar_Syntax_Syntax.sigel = uu____19572; FStar_Syntax_Syntax.sigrng = uu___275_19571.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___275_19571.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___275_19571.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___275_19571.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, t) -> begin
(

let uu____19577 = (elim_uvars_aux_t env us [] t)
in (match (uu____19577) with
| (us1, uu____19595, t1) -> begin
(

let uu___276_19609 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((l), (us1), (t1))); FStar_Syntax_Syntax.sigrng = uu___276_19609.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___276_19609.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___276_19609.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___276_19609.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____19610) -> begin
(failwith "Impossible: should have been desugared already")
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____19612 = (elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____19612) with
| (univs1, binders, signature) -> begin
(

let uu____19640 = (

let uu____19649 = (FStar_Syntax_Subst.univ_var_opening univs1)
in (match (uu____19649) with
| (univs_opening, univs2) -> begin
(

let uu____19676 = (FStar_Syntax_Subst.univ_var_closing univs2)
in ((univs_opening), (uu____19676)))
end))
in (match (uu____19640) with
| (univs_opening, univs_closing) -> begin
(

let uu____19693 = (

let binders1 = (FStar_Syntax_Subst.open_binders binders)
in (

let uu____19699 = (FStar_Syntax_Subst.opening_of_binders binders1)
in (

let uu____19700 = (FStar_Syntax_Subst.closing_of_binders binders1)
in ((uu____19699), (uu____19700)))))
in (match (uu____19693) with
| (b_opening, b_closing) -> begin
(

let n1 = (FStar_List.length univs1)
in (

let n_binders = (FStar_List.length binders)
in (

let elim_tscheme = (fun uu____19722 -> (match (uu____19722) with
| (us, t) -> begin
(

let n_us = (FStar_List.length us)
in (

let uu____19740 = (FStar_Syntax_Subst.open_univ_vars us t)
in (match (uu____19740) with
| (us1, t1) -> begin
(

let uu____19751 = (

let uu____19756 = (FStar_All.pipe_right b_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____19763 = (FStar_All.pipe_right b_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____19756), (uu____19763))))
in (match (uu____19751) with
| (b_opening1, b_closing1) -> begin
(

let uu____19776 = (

let uu____19781 = (FStar_All.pipe_right univs_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____19790 = (FStar_All.pipe_right univs_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____19781), (uu____19790))))
in (match (uu____19776) with
| (univs_opening1, univs_closing1) -> begin
(

let t2 = (

let uu____19806 = (FStar_Syntax_Subst.subst b_opening1 t1)
in (FStar_Syntax_Subst.subst univs_opening1 uu____19806))
in (

let uu____19807 = (elim_uvars_aux_t env [] [] t2)
in (match (uu____19807) with
| (uu____19828, uu____19829, t3) -> begin
(

let t4 = (

let uu____19844 = (

let uu____19845 = (FStar_Syntax_Subst.close_univ_vars us1 t3)
in (FStar_Syntax_Subst.subst b_closing1 uu____19845))
in (FStar_Syntax_Subst.subst univs_closing1 uu____19844))
in ((us1), (t4)))
end)))
end))
end))
end)))
end))
in (

let elim_term = (fun t -> (

let uu____19850 = (elim_uvars_aux_t env univs1 binders t)
in (match (uu____19850) with
| (uu____19863, uu____19864, t1) -> begin
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
| uu____19924 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((a.FStar_Syntax_Syntax.action_params), (body), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
end))
in (

let destruct_action_body = (fun body -> (

let uu____19941 = (

let uu____19942 = (FStar_Syntax_Subst.compress body)
in uu____19942.FStar_Syntax_Syntax.n)
in (match (uu____19941) with
| FStar_Syntax_Syntax.Tm_ascribed (defn, (FStar_Util.Inl (typ), FStar_Pervasives_Native.None), FStar_Pervasives_Native.None) -> begin
((defn), (typ))
end
| uu____20001 -> begin
(failwith "Impossible")
end)))
in (

let destruct_action_typ_templ = (fun t -> (

let uu____20030 = (

let uu____20031 = (FStar_Syntax_Subst.compress t)
in uu____20031.FStar_Syntax_Syntax.n)
in (match (uu____20030) with
| FStar_Syntax_Syntax.Tm_abs (pars, body, uu____20052) -> begin
(

let uu____20073 = (destruct_action_body body)
in (match (uu____20073) with
| (defn, typ) -> begin
((pars), (defn), (typ))
end))
end
| uu____20118 -> begin
(

let uu____20119 = (destruct_action_body t)
in (match (uu____20119) with
| (defn, typ) -> begin
(([]), (defn), (typ))
end))
end)))
in (

let uu____20168 = (elim_tscheme ((a.FStar_Syntax_Syntax.action_univs), (action_typ_templ)))
in (match (uu____20168) with
| (action_univs, t) -> begin
(

let uu____20177 = (destruct_action_typ_templ t)
in (match (uu____20177) with
| (action_params, action_defn, action_typ) -> begin
(

let a' = (

let uu___277_20218 = a
in {FStar_Syntax_Syntax.action_name = uu___277_20218.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___277_20218.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action_univs; FStar_Syntax_Syntax.action_params = action_params; FStar_Syntax_Syntax.action_defn = action_defn; FStar_Syntax_Syntax.action_typ = action_typ})
in a')
end))
end))))))
in (

let ed1 = (

let uu___278_20220 = ed
in (

let uu____20221 = (elim_tscheme ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____20222 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____20223 = (elim_tscheme ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____20224 = (elim_tscheme ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____20225 = (elim_tscheme ed.FStar_Syntax_Syntax.stronger)
in (

let uu____20226 = (elim_tscheme ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____20227 = (elim_tscheme ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____20228 = (elim_tscheme ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____20229 = (elim_tscheme ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____20230 = (elim_tscheme ed.FStar_Syntax_Syntax.trivial)
in (

let uu____20231 = (elim_term ed.FStar_Syntax_Syntax.repr)
in (

let uu____20232 = (elim_tscheme ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____20233 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____20234 = (FStar_List.map elim_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___278_20220.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___278_20220.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu____20221; FStar_Syntax_Syntax.bind_wp = uu____20222; FStar_Syntax_Syntax.if_then_else = uu____20223; FStar_Syntax_Syntax.ite_wp = uu____20224; FStar_Syntax_Syntax.stronger = uu____20225; FStar_Syntax_Syntax.close_wp = uu____20226; FStar_Syntax_Syntax.assert_p = uu____20227; FStar_Syntax_Syntax.assume_p = uu____20228; FStar_Syntax_Syntax.null_wp = uu____20229; FStar_Syntax_Syntax.trivial = uu____20230; FStar_Syntax_Syntax.repr = uu____20231; FStar_Syntax_Syntax.return_repr = uu____20232; FStar_Syntax_Syntax.bind_repr = uu____20233; FStar_Syntax_Syntax.actions = uu____20234})))))))))))))))
in (

let uu___279_20237 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ed1); FStar_Syntax_Syntax.sigrng = uu___279_20237.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___279_20237.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___279_20237.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___279_20237.FStar_Syntax_Syntax.sigattrs})))))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub_eff) -> begin
(

let elim_tscheme_opt = (fun uu___194_20254 -> (match (uu___194_20254) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (us, t) -> begin
(

let uu____20281 = (elim_uvars_aux_t env us [] t)
in (match (uu____20281) with
| (us1, uu____20305, t1) -> begin
FStar_Pervasives_Native.Some (((us1), (t1)))
end))
end))
in (

let sub_eff1 = (

let uu___280_20324 = sub_eff
in (

let uu____20325 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp)
in (

let uu____20328 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift)
in {FStar_Syntax_Syntax.source = uu___280_20324.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___280_20324.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = uu____20325; FStar_Syntax_Syntax.lift = uu____20328})))
in (

let uu___281_20331 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub_eff1); FStar_Syntax_Syntax.sigrng = uu___281_20331.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___281_20331.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___281_20331.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___281_20331.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univ_names, binders, comp, flags) -> begin
(

let uu____20341 = (elim_uvars_aux_c env univ_names binders comp)
in (match (uu____20341) with
| (univ_names1, binders1, comp1) -> begin
(

let uu___282_20375 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (univ_names1), (binders1), (comp1), (flags))); FStar_Syntax_Syntax.sigrng = uu___282_20375.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___282_20375.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___282_20375.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___282_20375.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_pragma (uu____20386) -> begin
s
end))




