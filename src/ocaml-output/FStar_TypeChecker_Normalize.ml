
open Prims
open FStar_Pervasives
type step =
| Beta
| Iota
| Zeta
| Exclude of step
| WHNF
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


let uu___is_WHNF : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| WHNF -> begin
true
end
| uu____48 -> begin
false
end))


let uu___is_Primops : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____53 -> begin
false
end))


let uu___is_Eager_unfolding : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding -> begin
true
end
| uu____58 -> begin
false
end))


let uu___is_Inlining : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____63 -> begin
false
end))


let uu___is_NoDeltaSteps : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoDeltaSteps -> begin
true
end
| uu____68 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____74 -> begin
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
| uu____90 -> begin
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
| uu____109 -> begin
false
end))


let uu___is_PureSubtermsWithinComputations : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PureSubtermsWithinComputations -> begin
true
end
| uu____114 -> begin
false
end))


let uu___is_Simplify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simplify -> begin
true
end
| uu____119 -> begin
false
end))


let uu___is_EraseUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EraseUniverses -> begin
true
end
| uu____124 -> begin
false
end))


let uu___is_AllowUnboundUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AllowUnboundUniverses -> begin
true
end
| uu____129 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____134 -> begin
false
end))


let uu___is_CompressUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CompressUvars -> begin
true
end
| uu____139 -> begin
false
end))


let uu___is_NoFullNorm : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoFullNorm -> begin
true
end
| uu____144 -> begin
false
end))


let uu___is_CheckNoUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckNoUvars -> begin
true
end
| uu____149 -> begin
false
end))


type steps =
step Prims.list

type primitive_step =
{name : FStar_Ident.lid; arity : Prims.int; strong_reduction_ok : Prims.bool; interpretation : FStar_Range.range  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option}


let __proj__Mkprimitive_step__item__name : primitive_step  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; strong_reduction_ok = __fname__strong_reduction_ok; interpretation = __fname__interpretation} -> begin
__fname__name
end))


let __proj__Mkprimitive_step__item__arity : primitive_step  ->  Prims.int = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; strong_reduction_ok = __fname__strong_reduction_ok; interpretation = __fname__interpretation} -> begin
__fname__arity
end))


let __proj__Mkprimitive_step__item__strong_reduction_ok : primitive_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; strong_reduction_ok = __fname__strong_reduction_ok; interpretation = __fname__interpretation} -> begin
__fname__strong_reduction_ok
end))


let __proj__Mkprimitive_step__item__interpretation : primitive_step  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; strong_reduction_ok = __fname__strong_reduction_ok; interpretation = __fname__interpretation} -> begin
__fname__interpretation
end))

type closure =
| Clos of (closure Prims.list * FStar_Syntax_Syntax.term * (closure Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
| Univ of FStar_Syntax_Syntax.universe
| Dummy


let uu___is_Clos : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Clos (_0) -> begin
true
end
| uu____297 -> begin
false
end))


let __proj__Clos__item___0 : closure  ->  (closure Prims.list * FStar_Syntax_Syntax.term * (closure Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool) = (fun projectee -> (match (projectee) with
| Clos (_0) -> begin
_0
end))


let uu___is_Univ : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Univ (_0) -> begin
true
end
| uu____365 -> begin
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
| uu____378 -> begin
false
end))


type env =
closure Prims.list


let closure_to_string : closure  ->  Prims.string = (fun uu___140_384 -> (match (uu___140_384) with
| Clos (uu____385, t, uu____387, uu____388) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| Univ (uu____409) -> begin
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


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list


type subst_t =
FStar_Syntax_Syntax.subst_elt Prims.list

type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option * FStar_Range.range)
| App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range)
| Let of (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range)
| Steps of (steps * primitive_step Prims.list * FStar_TypeChecker_Env.delta_level Prims.list)
| Debug of FStar_Syntax_Syntax.term


let uu___is_Arg : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Arg (_0) -> begin
true
end
| uu____614 -> begin
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
| uu____652 -> begin
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
| uu____690 -> begin
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
| uu____731 -> begin
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
| uu____775 -> begin
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
| uu____831 -> begin
false
end))


let __proj__App__item___0 : stack_elt  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| App (_0) -> begin
_0
end))


let uu___is_Meta : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
true
end
| uu____867 -> begin
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
| uu____901 -> begin
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
| uu____949 -> begin
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
| uu____993 -> begin
false
end))


let __proj__Debug__item___0 : stack_elt  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
_0
end))


type stack =
stack_elt Prims.list


let mk : 'Auu____1010 . 'Auu____1010  ->  FStar_Range.range  ->  'Auu____1010 FStar_Syntax_Syntax.syntax = (fun t r -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r))


let set_memo : 'Auu____1028 . 'Auu____1028 FStar_Pervasives_Native.option FStar_ST.ref  ->  'Auu____1028  ->  Prims.unit = (fun r t -> (

let uu____1047 = (FStar_ST.read r)
in (match (uu____1047) with
| FStar_Pervasives_Native.Some (uu____1054) -> begin
(failwith "Unexpected set_memo: thunk already evaluated")
end
| FStar_Pervasives_Native.None -> begin
(FStar_ST.write r (FStar_Pervasives_Native.Some (t)))
end)))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (

let uu____1067 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right uu____1067 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun uu___141_1075 -> (match (uu___141_1075) with
| Arg (c, uu____1077, uu____1078) -> begin
(

let uu____1079 = (closure_to_string c)
in (FStar_Util.format1 "Closure %s" uu____1079))
end
| MemoLazy (uu____1080) -> begin
"MemoLazy"
end
| Abs (uu____1087, bs, uu____1089, uu____1090, uu____1091) -> begin
(

let uu____1096 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" uu____1096))
end
| UnivArgs (uu____1101) -> begin
"UnivArgs"
end
| Match (uu____1108) -> begin
"Match"
end
| App (t, uu____1116, uu____1117) -> begin
(

let uu____1118 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "App %s" uu____1118))
end
| Meta (m, uu____1120) -> begin
"Meta"
end
| Let (uu____1121) -> begin
"Let"
end
| Steps (uu____1130, uu____1131, uu____1132) -> begin
"Steps"
end
| Debug (t) -> begin
(

let uu____1142 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Debug %s" uu____1142))
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (

let uu____1151 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right uu____1151 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> (

let uu____1169 = (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm")))
in (match (uu____1169) with
| true -> begin
(f ())
end
| uu____1170 -> begin
()
end)))


let is_empty : 'Auu____1175 . 'Auu____1175 Prims.list  ->  Prims.bool = (fun uu___142_1181 -> (match (uu___142_1181) with
| [] -> begin
true
end
| uu____1184 -> begin
false
end))


let lookup_bvar : 'Auu____1193 . 'Auu____1193 Prims.list  ->  FStar_Syntax_Syntax.bv  ->  'Auu____1193 = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| uu____1212 -> begin
(

let uu____1213 = (

let uu____1214 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" uu____1214))
in (failwith uu____1213))
end)


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun l -> (match ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Pure_lid)
end
| uu____1223 -> begin
(match ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Tot_lid)
end
| uu____1226 -> begin
(match ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_PURE_lid)
end
| uu____1229 -> begin
FStar_Pervasives_Native.None
end)
end)
end))


let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us1 = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let uu____1259 = (FStar_List.fold_left (fun uu____1285 u1 -> (match (uu____1285) with
| (cur_kernel, cur_max, out) -> begin
(

let uu____1310 = (FStar_Syntax_Util.univ_kernel u1)
in (match (uu____1310) with
| (k_u, n1) -> begin
(

let uu____1325 = (FStar_Syntax_Util.eq_univs cur_kernel k_u)
in (match (uu____1325) with
| true -> begin
((cur_kernel), (u1), (out))
end
| uu____1336 -> begin
((k_u), (u1), ((cur_max)::out))
end))
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us1)
in (match (uu____1259) with
| (uu____1343, u1, out) -> begin
(FStar_List.rev ((u1)::out))
end))))
in (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
try
(match (()) with
| () -> begin
(

let uu____1368 = (FStar_List.nth env x)
in (match (uu____1368) with
| Univ (u3) -> begin
(aux u3)
end
| Dummy -> begin
(u2)::[]
end
| uu____1372 -> begin
(failwith "Impossible: universe variable bound to a term")
end))
end)
with
| uu____1381 -> begin
(

let uu____1382 = (FStar_All.pipe_right cfg.steps (FStar_List.contains AllowUnboundUniverses))
in (match (uu____1382) with
| true -> begin
(FStar_Syntax_Syntax.U_unknown)::[]
end
| uu____1385 -> begin
(failwith "Universe variable not found")
end))
end
end
| FStar_Syntax_Syntax.U_unif (uu____1388) when (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars)) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_zero -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_unif (uu____1397) -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_name (uu____1406) -> begin
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

let uu____1413 = (FStar_List.collect aux us)
in (FStar_All.pipe_right uu____1413 norm_univs))
in (match (us1) with
| (u_k)::(hd1)::rest -> begin
(

let rest1 = (hd1)::rest
in (

let uu____1430 = (FStar_Syntax_Util.univ_kernel u_k)
in (match (uu____1430) with
| (FStar_Syntax_Syntax.U_zero, n1) -> begin
(

let uu____1438 = (FStar_All.pipe_right rest1 (FStar_List.for_all (fun u3 -> (

let uu____1446 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____1446) with
| (uu____1451, m) -> begin
(n1 <= m)
end)))))
in (match (uu____1438) with
| true -> begin
rest1
end
| uu____1455 -> begin
us1
end))
end
| uu____1456 -> begin
us1
end)))
end
| uu____1461 -> begin
us1
end))
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1465 = (aux u3)
in (FStar_List.map (fun _0_40 -> FStar_Syntax_Syntax.U_succ (_0_40)) uu____1465))
end)))
in (

let uu____1468 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____1468) with
| true -> begin
FStar_Syntax_Syntax.U_unknown
end
| uu____1469 -> begin
(

let uu____1470 = (aux u)
in (match (uu____1470) with
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


let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> ((log cfg (fun uu____1590 -> (

let uu____1591 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1592 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1591 uu____1592)))));
(match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| uu____1593 -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1597) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t1
end
| FStar_Syntax_Syntax.Tm_constant (uu____1622) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_name (uu____1623) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1624) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1625) -> begin
(

let uu____1642 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____1642) with
| true -> begin
(

let uu____1643 = (

let uu____1644 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____1645 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s): CheckNoUvars: Unexpected unification variable remains: %s" uu____1644 uu____1645)))
in (failwith uu____1643))
end
| uu____1646 -> begin
t1
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____1648 = (

let uu____1649 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (uu____1649))
in (mk uu____1648 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let uu____1656 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1656))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____1658 = (lookup_bvar env x)
in (match (uu____1658) with
| Univ (uu____1659) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t1
end
| Clos (env1, t0, r, uu____1663) -> begin
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

let uu____1751 = (closures_as_binders_delayed cfg env bs)
in (match (uu____1751) with
| (bs1, env1) -> begin
(

let body1 = (closure_as_term_delayed cfg env1 body)
in (

let uu____1785 = (

let uu____1786 = (

let uu____1803 = (close_lcomp_opt cfg env1 lopt)
in ((bs1), (body1), (uu____1803)))
in FStar_Syntax_Syntax.Tm_abs (uu____1786))
in (mk uu____1785 t1.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1834 = (closures_as_binders_delayed cfg env bs)
in (match (uu____1834) with
| (bs1, env1) -> begin
(

let c1 = (close_comp cfg env1 c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs1), (c1)))) t1.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____1882 = (

let uu____1895 = (

let uu____1902 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1902)::[])
in (closures_as_binders_delayed cfg env uu____1895))
in (match (uu____1882) with
| (x1, env1) -> begin
(

let phi1 = (closure_as_term_delayed cfg env1 phi)
in (

let uu____1924 = (

let uu____1925 = (

let uu____1932 = (

let uu____1933 = (FStar_List.hd x1)
in (FStar_All.pipe_right uu____1933 FStar_Pervasives_Native.fst))
in ((uu____1932), (phi1)))
in FStar_Syntax_Syntax.Tm_refine (uu____1925))
in (mk uu____1924 t1.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (annot, tacopt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____2024 = (closure_as_term_delayed cfg env t2)
in FStar_Util.Inl (uu____2024))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2038 = (close_comp cfg env c)
in FStar_Util.Inr (uu____2038))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (closure_as_term_delayed cfg env))
in (

let uu____2054 = (

let uu____2055 = (

let uu____2082 = (closure_as_term_delayed cfg env t11)
in ((uu____2082), (((annot1), (tacopt1))), (lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2055))
in (mk uu____2054 t1.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____2133 = (

let uu____2134 = (

let uu____2141 = (closure_as_term_delayed cfg env t')
in (

let uu____2144 = (

let uu____2145 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (uu____2145))
in ((uu____2141), (uu____2144))))
in FStar_Syntax_Syntax.Tm_meta (uu____2134))
in (mk uu____2133 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(

let uu____2205 = (

let uu____2206 = (

let uu____2213 = (closure_as_term_delayed cfg env t')
in (

let uu____2216 = (

let uu____2217 = (

let uu____2224 = (closure_as_term_delayed cfg env tbody)
in ((m), (uu____2224)))
in FStar_Syntax_Syntax.Meta_monadic (uu____2217))
in ((uu____2213), (uu____2216))))
in FStar_Syntax_Syntax.Tm_meta (uu____2206))
in (mk uu____2205 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody)) -> begin
(

let uu____2243 = (

let uu____2244 = (

let uu____2251 = (closure_as_term_delayed cfg env t')
in (

let uu____2254 = (

let uu____2255 = (

let uu____2264 = (closure_as_term_delayed cfg env tbody)
in ((m1), (m2), (uu____2264)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____2255))
in ((uu____2251), (uu____2254))))
in FStar_Syntax_Syntax.Tm_meta (uu____2244))
in (mk uu____2243 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(

let uu____2277 = (

let uu____2278 = (

let uu____2285 = (closure_as_term_delayed cfg env t')
in ((uu____2285), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____2278))
in (mk uu____2277 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env1 = (FStar_List.fold_left (fun env1 uu____2315 -> (Dummy)::env1) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____2322 = (

let uu____2333 = (FStar_Syntax_Syntax.is_top_level ((lb)::[]))
in (match (uu____2333) with
| true -> begin
((lb.FStar_Syntax_Syntax.lbname), (body))
end
| uu____2350 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2352 = (closure_as_term cfg ((Dummy)::env0) body)
in ((FStar_Util.Inl ((

let uu___159_2358 = x
in {FStar_Syntax_Syntax.ppname = uu___159_2358.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___159_2358.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = typ}))), (uu____2352))))
end))
in (match (uu____2322) with
| (nm, body1) -> begin
(

let lb1 = (

let uu___160_2374 = lb
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___160_2374.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = uu___160_2374.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (body1)))) t1.FStar_Syntax_Syntax.pos))
end))))))
end
| FStar_Syntax_Syntax.Tm_let ((uu____2385, lbs), body) -> begin
(

let norm_one_lb = (fun env1 lb -> (

let env_univs = (FStar_List.fold_right (fun uu____2420 env2 -> (Dummy)::env2) lb.FStar_Syntax_Syntax.lbunivs env1)
in (

let env2 = (

let uu____2427 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____2427) with
| true -> begin
env_univs
end
| uu____2430 -> begin
(FStar_List.fold_right (fun uu____2435 env2 -> (Dummy)::env2) lbs env_univs)
end))
in (

let ty = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (

let nm = (

let uu____2445 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____2445) with
| true -> begin
lb.FStar_Syntax_Syntax.lbname
end
| uu____2450 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_All.pipe_right (

let uu___161_2457 = x
in {FStar_Syntax_Syntax.ppname = uu___161_2457.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___161_2457.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty}) (fun _0_41 -> FStar_Util.Inl (_0_41))))
end))
in (

let uu___162_2458 = lb
in (

let uu____2459 = (closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___162_2458.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___162_2458.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____2459})))))))
in (

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body1 = (

let body_env = (FStar_List.fold_right (fun uu____2477 env1 -> (Dummy)::env1) lbs1 env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs1))), (body1)))) t1.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let head2 = (closure_as_term cfg env head1)
in (

let norm_one_branch = (fun env1 uu____2556 -> (match (uu____2556) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____2621) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2644 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____2710 uu____2711 -> (match (((uu____2710), (uu____2711))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____2814 = (norm_pat env3 p1)
in (match (uu____2814) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____2644) with
| (pats1, env3) -> begin
(((

let uu___163_2916 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___163_2916.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___164_2935 = x
in (

let uu____2936 = (closure_as_term cfg env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___164_2935.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___164_2935.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2936}))
in (((

let uu___165_2944 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___165_2944.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___166_2949 = x
in (

let uu____2950 = (closure_as_term cfg env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___166_2949.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___166_2949.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2950}))
in (((

let uu___167_2958 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___167_2958.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t2) -> begin
(

let x1 = (

let uu___168_2968 = x
in (

let uu____2969 = (closure_as_term cfg env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___168_2968.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___168_2968.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2969}))
in (

let t3 = (closure_as_term cfg env2 t2)
in (((

let uu___169_2978 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t3))); FStar_Syntax_Syntax.p = uu___169_2978.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let uu____2981 = (norm_pat env1 pat)
in (match (uu____2981) with
| (pat1, env2) -> begin
(

let w_opt1 = (match (w_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____3016 = (closure_as_term cfg env2 w)
in FStar_Pervasives_Native.Some (uu____3016))
end)
in (

let tm1 = (closure_as_term cfg env2 tm)
in ((pat1), (w_opt1), (tm1))))
end)))
end))
in (

let uu____3022 = (

let uu____3023 = (

let uu____3046 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head2), (uu____3046)))
in FStar_Syntax_Syntax.Tm_match (uu____3023))
in (mk uu____3022 t1.FStar_Syntax_Syntax.pos))))
end))
end);
))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| uu____3128 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| uu____3152 -> begin
(FStar_List.map (fun uu____3171 -> (match (uu____3171) with
| (x, imp) -> begin
(

let uu____3190 = (closure_as_term_delayed cfg env x)
in ((uu____3190), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * closure Prims.list) = (fun cfg env bs -> (

let uu____3206 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____3261 uu____3262 -> (match (((uu____3261), (uu____3262))) with
| ((env1, out), (b, imp)) -> begin
(

let b1 = (

let uu___170_3344 = b
in (

let uu____3345 = (closure_as_term_delayed cfg env1 b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___170_3344.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___170_3344.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3345}))
in (

let env2 = (Dummy)::env1
in ((env2), ((((b1), (imp)))::out))))
end)) ((env), ([]))))
in (match (uu____3206) with
| (env1, bs1) -> begin
(((FStar_List.rev bs1)), (env1))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| uu____3426 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____3441 = (closure_as_term_delayed cfg env t)
in (

let uu____3442 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____3441 uu____3442)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____3455 = (closure_as_term_delayed cfg env t)
in (

let uu____3456 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____3455 uu____3456)))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let rt = (closure_as_term_delayed cfg env c1.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c1.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___143_3482 -> (match (uu___143_3482) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____3486 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (uu____3486))
end
| f -> begin
f
end))))
in (

let uu____3490 = (

let uu___171_3491 = c1
in (

let uu____3492 = (FStar_List.map (norm_universe cfg env) c1.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = uu____3492; FStar_Syntax_Syntax.effect_name = uu___171_3491.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp uu____3490)))))
end)
end))
and filter_out_lcomp_cflags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun flags -> (FStar_All.pipe_right flags (FStar_List.filter (fun uu___144_3502 -> (match (uu___144_3502) with
| FStar_Syntax_Syntax.DECREASES (uu____3503) -> begin
false
end
| uu____3506 -> begin
true
end)))))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.filter (fun uu___145_3526 -> (match (uu___145_3526) with
| FStar_Syntax_Syntax.DECREASES (uu____3527) -> begin
false
end
| uu____3530 -> begin
true
end))))
in (

let rc1 = (

let uu___172_3532 = rc
in (

let uu____3533 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (closure_as_term cfg env))
in {FStar_Syntax_Syntax.residual_effect = uu___172_3532.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____3533; FStar_Syntax_Syntax.residual_flags = flags}))
in FStar_Pervasives_Native.Some (rc1)))
end
| uu____3540 -> begin
lopt
end))


let built_in_primitive_steps : primitive_step Prims.list = (

let const_as_tm = (fun c p -> (mk (FStar_Syntax_Syntax.Tm_constant (c)) p))
in (

let int_as_const = (fun p i -> (

let uu____3561 = (

let uu____3562 = (

let uu____3573 = (FStar_Util.string_of_int i)
in ((uu____3573), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____3562))
in (const_as_tm uu____3561 p)))
in (

let bool_as_const = (fun p b -> (const_as_tm (FStar_Const.Const_bool (b)) p))
in (

let string_as_const = (fun p b -> (const_as_tm (FStar_Const.Const_string ((((FStar_Util.bytes_of_string b)), (p)))) p))
in (

let arg_as_int = (fun uu____3609 -> (match (uu____3609) with
| (a, uu____3617) -> begin
(

let uu____3620 = (

let uu____3621 = (FStar_Syntax_Subst.compress a)
in uu____3621.FStar_Syntax_Syntax.n)
in (match (uu____3620) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, FStar_Pervasives_Native.None)) -> begin
(

let uu____3637 = (FStar_Util.int_of_string i)
in FStar_Pervasives_Native.Some (uu____3637))
end
| uu____3638 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_bounded_int = (fun uu____3652 -> (match (uu____3652) with
| (a, uu____3664) -> begin
(

let uu____3671 = (

let uu____3672 = (FStar_Syntax_Subst.compress a)
in uu____3672.FStar_Syntax_Syntax.n)
in (match (uu____3671) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv1); FStar_Syntax_Syntax.pos = uu____3682; FStar_Syntax_Syntax.vars = uu____3683}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, FStar_Pervasives_Native.None)); FStar_Syntax_Syntax.pos = uu____3685; FStar_Syntax_Syntax.vars = uu____3686}, uu____3687))::[]) when (FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") -> begin
(

let uu____3726 = (

let uu____3731 = (FStar_Util.int_of_string i)
in ((fv1), (uu____3731)))
in FStar_Pervasives_Native.Some (uu____3726))
end
| uu____3736 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_bool = (fun uu____3750 -> (match (uu____3750) with
| (a, uu____3758) -> begin
(

let uu____3761 = (

let uu____3762 = (FStar_Syntax_Subst.compress a)
in uu____3762.FStar_Syntax_Syntax.n)
in (match (uu____3761) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (b)) -> begin
FStar_Pervasives_Native.Some (b)
end
| uu____3768 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_char = (fun uu____3778 -> (match (uu____3778) with
| (a, uu____3786) -> begin
(

let uu____3789 = (

let uu____3790 = (FStar_Syntax_Subst.compress a)
in uu____3790.FStar_Syntax_Syntax.n)
in (match (uu____3789) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c)) -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____3796 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_string = (fun uu____3806 -> (match (uu____3806) with
| (a, uu____3814) -> begin
(

let uu____3817 = (

let uu____3818 = (FStar_Syntax_Subst.compress a)
in uu____3818.FStar_Syntax_Syntax.n)
in (match (uu____3817) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (bytes, uu____3824)) -> begin
FStar_Pervasives_Native.Some ((FStar_Util.string_of_bytes bytes))
end
| uu____3829 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_list = (fun f uu____3855 -> (match (uu____3855) with
| (a, uu____3869) -> begin
(

let rec sequence = (fun l -> (match (l) with
| [] -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Pervasives_Native.None)::uu____3898 -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.Some (x))::xs -> begin
(

let uu____3915 = (sequence xs)
in (match (uu____3915) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (xs') -> begin
FStar_Pervasives_Native.Some ((x)::xs')
end))
end))
in (

let uu____3935 = (FStar_Syntax_Util.list_elements a)
in (match (uu____3935) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (elts) -> begin
(

let uu____3953 = (FStar_List.map (fun x -> (

let uu____3963 = (FStar_Syntax_Syntax.as_arg x)
in (f uu____3963))) elts)
in (sequence uu____3953))
end)))
end))
in (

let lift_unary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a))::[] -> begin
(

let uu____4001 = (f a)
in FStar_Pervasives_Native.Some (uu____4001))
end
| uu____4002 -> begin
FStar_Pervasives_Native.None
end))
in (

let lift_binary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a0))::(FStar_Pervasives_Native.Some (a1))::[] -> begin
(

let uu____4052 = (f a0 a1)
in FStar_Pervasives_Native.Some (uu____4052))
end
| uu____4053 -> begin
FStar_Pervasives_Native.None
end))
in (

let unary_op = (fun as_a f r args -> (

let uu____4102 = (FStar_List.map as_a args)
in (lift_unary (f r) uu____4102)))
in (

let binary_op = (fun as_a f r args -> (

let uu____4158 = (FStar_List.map as_a args)
in (lift_binary (f r) uu____4158)))
in (

let as_primitive_step = (fun uu____4182 -> (match (uu____4182) with
| (l, arity, f) -> begin
{name = l; arity = arity; strong_reduction_ok = true; interpretation = f}
end))
in (

let unary_int_op = (fun f -> (unary_op arg_as_int (fun r x -> (

let uu____4230 = (f x)
in (int_as_const r uu____4230)))))
in (

let binary_int_op = (fun f -> (binary_op arg_as_int (fun r x y -> (

let uu____4258 = (f x y)
in (int_as_const r uu____4258)))))
in (

let unary_bool_op = (fun f -> (unary_op arg_as_bool (fun r x -> (

let uu____4279 = (f x)
in (bool_as_const r uu____4279)))))
in (

let binary_bool_op = (fun f -> (binary_op arg_as_bool (fun r x y -> (

let uu____4307 = (f x y)
in (bool_as_const r uu____4307)))))
in (

let binary_string_op = (fun f -> (binary_op arg_as_string (fun r x y -> (

let uu____4335 = (f x y)
in (string_as_const r uu____4335)))))
in (

let list_of_string' = (fun rng s -> (

let name = (fun l -> (

let uu____4349 = (

let uu____4350 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____4350))
in (mk uu____4349 rng)))
in (

let char_t = (name FStar_Parser_Const.char_lid)
in (

let charterm = (fun c -> (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))) rng))
in (

let uu____4360 = (

let uu____4363 = (FStar_String.list_of_string s)
in (FStar_List.map charterm uu____4363))
in (FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4360))))))
in (

let string_of_list' = (fun rng l -> (

let s = (FStar_String.string_of_list l)
in (FStar_Syntax_Util.exp_string s)))
in (

let string_compare' = (fun rng s1 s2 -> (

let r = (FStar_String.compare s1 s2)
in (int_as_const rng r)))
in (

let string_concat' = (fun rng args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____4438 = (arg_as_string a1)
in (match (uu____4438) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____4444 = (arg_as_list arg_as_string a2)
in (match (uu____4444) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.concat s1 s2)
in (

let uu____4457 = (string_as_const rng r)
in FStar_Pervasives_Native.Some (uu____4457)))
end
| uu____4458 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4463 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4466 -> begin
FStar_Pervasives_Native.None
end))
in (

let string_of_int1 = (fun rng i -> (

let uu____4480 = (FStar_Util.string_of_int i)
in (string_as_const rng uu____4480)))
in (

let string_of_bool1 = (fun rng b -> (string_as_const rng (match (b) with
| true -> begin
"true"
end
| uu____4488 -> begin
"false"
end)))
in (

let string_of_int2 = (fun rng i -> (

let uu____4496 = (FStar_Util.string_of_int i)
in (string_as_const rng uu____4496)))
in (

let string_of_bool2 = (fun rng b -> (string_as_const rng (match (b) with
| true -> begin
"true"
end
| uu____4504 -> begin
"false"
end)))
in (

let term_of_range = (fun r -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r))) FStar_Pervasives_Native.None r))
in (

let range_of1 = (fun uu____4526 args -> (match (args) with
| (uu____4538)::((t, uu____4540))::[] -> begin
(

let uu____4569 = (term_of_range t.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (uu____4569))
end
| uu____4574 -> begin
FStar_Pervasives_Native.None
end))
in (

let set_range_of1 = (fun r args -> (match (args) with
| (uu____4612)::((t, uu____4614))::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)); FStar_Syntax_Syntax.pos = uu____4616; FStar_Syntax_Syntax.vars = uu____4617}, uu____4618))::[] -> begin
FStar_Pervasives_Native.Some ((

let uu___173_4660 = t
in {FStar_Syntax_Syntax.n = uu___173_4660.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___173_4660.FStar_Syntax_Syntax.vars}))
end
| uu____4663 -> begin
FStar_Pervasives_Native.None
end))
in (

let mk_range1 = (fun r args -> (match (args) with
| (fn)::(from_line)::(from_col)::(to_line)::(to_col)::[] -> begin
(

let uu____4744 = (

let uu____4765 = (arg_as_string fn)
in (

let uu____4768 = (arg_as_int from_line)
in (

let uu____4771 = (arg_as_int from_col)
in (

let uu____4774 = (arg_as_int to_line)
in (

let uu____4777 = (arg_as_int to_col)
in ((uu____4765), (uu____4768), (uu____4771), (uu____4774), (uu____4777)))))))
in (match (uu____4744) with
| (FStar_Pervasives_Native.Some (fn1), FStar_Pervasives_Native.Some (from_l), FStar_Pervasives_Native.Some (from_c), FStar_Pervasives_Native.Some (to_l), FStar_Pervasives_Native.Some (to_c)) -> begin
(

let r1 = (

let uu____4808 = (FStar_Range.mk_pos from_l from_c)
in (

let uu____4809 = (FStar_Range.mk_pos to_l to_c)
in (FStar_Range.mk_range fn1 uu____4808 uu____4809)))
in (

let uu____4810 = (term_of_range r1)
in FStar_Pervasives_Native.Some (uu____4810)))
end
| uu____4815 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4836 -> begin
FStar_Pervasives_Native.None
end))
in (

let decidable_eq = (fun neg rng args -> (

let tru = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) rng)
in (

let fal = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) rng)
in (match (args) with
| ((_typ, uu____4866))::((a1, uu____4868))::((a2, uu____4870))::[] -> begin
(

let uu____4907 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____4907) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
fal
end
| uu____4914 -> begin
tru
end))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
tru
end
| uu____4919 -> begin
fal
end))
end
| uu____4920 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4921 -> begin
(failwith "Unexpected number of arguments")
end))))
in (

let basic_ops = (

let uu____4939 = (

let uu____4954 = (

let uu____4969 = (

let uu____4984 = (

let uu____4999 = (

let uu____5014 = (

let uu____5029 = (

let uu____5044 = (

let uu____5059 = (

let uu____5074 = (

let uu____5089 = (

let uu____5104 = (

let uu____5119 = (

let uu____5134 = (

let uu____5149 = (

let uu____5164 = (

let uu____5179 = (

let uu____5194 = (

let uu____5209 = (

let uu____5224 = (

let uu____5239 = (

let uu____5252 = (FStar_Parser_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((uu____5252), ((Prims.parse_int "1")), ((unary_op arg_as_string list_of_string'))))
in (

let uu____5259 = (

let uu____5274 = (

let uu____5287 = (FStar_Parser_Const.p2l (("FStar")::("String")::("string_of_list")::[]))
in ((uu____5287), ((Prims.parse_int "1")), ((unary_op (arg_as_list arg_as_char) string_of_list'))))
in (

let uu____5296 = (

let uu____5311 = (

let uu____5330 = (FStar_Parser_Const.p2l (("FStar")::("String")::("concat")::[]))
in ((uu____5330), ((Prims.parse_int "2")), (string_concat')))
in (

let uu____5343 = (

let uu____5364 = (

let uu____5385 = (FStar_Parser_Const.p2l (("Prims")::("range_of")::[]))
in ((uu____5385), ((Prims.parse_int "2")), (range_of1)))
in (

let uu____5400 = (

let uu____5423 = (

let uu____5444 = (FStar_Parser_Const.p2l (("Prims")::("set_range_of")::[]))
in ((uu____5444), ((Prims.parse_int "3")), (set_range_of1)))
in (

let uu____5459 = (

let uu____5482 = (

let uu____5501 = (FStar_Parser_Const.p2l (("Prims")::("mk_range")::[]))
in ((uu____5501), ((Prims.parse_int "5")), (mk_range1)))
in (uu____5482)::[])
in (uu____5423)::uu____5459))
in (uu____5364)::uu____5400))
in (uu____5311)::uu____5343))
in (uu____5274)::uu____5296))
in (uu____5239)::uu____5259))
in (((FStar_Parser_Const.op_notEq), ((Prims.parse_int "3")), ((decidable_eq true))))::uu____5224)
in (((FStar_Parser_Const.op_Eq), ((Prims.parse_int "3")), ((decidable_eq false))))::uu____5209)
in (((FStar_Parser_Const.string_compare), ((Prims.parse_int "2")), ((binary_op arg_as_string string_compare'))))::uu____5194)
in (((FStar_Parser_Const.string_of_bool_lid), ((Prims.parse_int "1")), ((unary_op arg_as_bool string_of_bool2))))::uu____5179)
in (((FStar_Parser_Const.string_of_int_lid), ((Prims.parse_int "1")), ((unary_op arg_as_int string_of_int2))))::uu____5164)
in (((FStar_Parser_Const.strcat_lid'), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____5149)
in (((FStar_Parser_Const.strcat_lid), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____5134)
in (((FStar_Parser_Const.op_Or), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x || y))))))::uu____5119)
in (((FStar_Parser_Const.op_And), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x && y))))))::uu____5104)
in (((FStar_Parser_Const.op_Negation), ((Prims.parse_int "1")), ((unary_bool_op (fun x -> (not (x)))))))::uu____5089)
in (((FStar_Parser_Const.op_Modulus), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x mod y))))))::uu____5074)
in (((FStar_Parser_Const.op_GTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x >= y)))))))::uu____5059)
in (((FStar_Parser_Const.op_GT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x > y)))))))::uu____5044)
in (((FStar_Parser_Const.op_LTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x <= y)))))))::uu____5029)
in (((FStar_Parser_Const.op_LT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x < y)))))))::uu____5014)
in (((FStar_Parser_Const.op_Division), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x / y))))))::uu____4999)
in (((FStar_Parser_Const.op_Multiply), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x * y))))))::uu____4984)
in (((FStar_Parser_Const.op_Subtraction), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x - y))))))::uu____4969)
in (((FStar_Parser_Const.op_Addition), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x + y))))))::uu____4954)
in (((FStar_Parser_Const.op_Minus), ((Prims.parse_int "1")), ((unary_int_op (fun x -> (~- (x)))))))::uu____4939)
in (

let bounded_arith_ops = (

let bounded_int_types = ("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]
in (

let int_as_bounded = (fun r int_to_t1 n1 -> (

let c = (int_as_const r n1)
in (

let int_to_t2 = (FStar_Syntax_Syntax.fv_to_tm int_to_t1)
in (

let uu____6108 = (

let uu____6109 = (

let uu____6110 = (FStar_Syntax_Syntax.as_arg c)
in (uu____6110)::[])
in (FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6109))
in (uu____6108 FStar_Pervasives_Native.None r)))))
in (FStar_All.pipe_right bounded_int_types (FStar_List.collect (fun m -> (

let uu____6145 = (

let uu____6158 = (FStar_Parser_Const.p2l (("FStar")::(m)::("add")::[]))
in ((uu____6158), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____6177 uu____6178 -> (match (((uu____6177), (uu____6178))) with
| ((int_to_t1, x), (uu____6197, y)) -> begin
(int_as_bounded r int_to_t1 (x + y))
end))))))
in (

let uu____6207 = (

let uu____6222 = (

let uu____6235 = (FStar_Parser_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((uu____6235), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____6254 uu____6255 -> (match (((uu____6254), (uu____6255))) with
| ((int_to_t1, x), (uu____6274, y)) -> begin
(int_as_bounded r int_to_t1 (x - y))
end))))))
in (

let uu____6284 = (

let uu____6299 = (

let uu____6312 = (FStar_Parser_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((uu____6312), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____6331 uu____6332 -> (match (((uu____6331), (uu____6332))) with
| ((int_to_t1, x), (uu____6351, y)) -> begin
(int_as_bounded r int_to_t1 (x * y))
end))))))
in (uu____6299)::[])
in (uu____6222)::uu____6284))
in (uu____6145)::uu____6207)))))))
in (FStar_List.map as_primitive_step (FStar_List.append basic_ops bounded_arith_ops)))))))))))))))))))))))))))))))))))))


let equality_ops : primitive_step Prims.list = (

let interp_prop = (fun r args -> (match (args) with
| ((_typ, uu____6447))::((a1, uu____6449))::((a2, uu____6451))::[] -> begin
(

let uu____6488 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____6488) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___174_6494 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___174_6494.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___174_6494.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___175_6498 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___175_6498.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___175_6498.FStar_Syntax_Syntax.vars}))
end
| uu____6499 -> begin
FStar_Pervasives_Native.None
end))
end
| ((_typ, uu____6501))::(uu____6502)::((a1, uu____6504))::((a2, uu____6506))::[] -> begin
(

let uu____6555 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____6555) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___174_6561 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___174_6561.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___174_6561.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___175_6565 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___175_6565.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___175_6565.FStar_Syntax_Syntax.vars}))
end
| uu____6566 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____6567 -> begin
(failwith "Unexpected number of arguments")
end))
in (

let propositional_equality = {name = FStar_Parser_Const.eq2_lid; arity = (Prims.parse_int "3"); strong_reduction_ok = true; interpretation = interp_prop}
in (

let hetero_propositional_equality = {name = FStar_Parser_Const.eq3_lid; arity = (Prims.parse_int "4"); strong_reduction_ok = true; interpretation = interp_prop}
in (propositional_equality)::(hetero_propositional_equality)::[])))


let reduce_primops : cfg  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (

let uu____6580 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops cfg.steps))
in (match (uu____6580) with
| true -> begin
tm
end
| uu____6581 -> begin
(

let uu____6582 = (FStar_Syntax_Util.head_and_args tm)
in (match (uu____6582) with
| (head1, args) -> begin
(

let uu____6619 = (

let uu____6620 = (FStar_Syntax_Util.un_uinst head1)
in uu____6620.FStar_Syntax_Syntax.n)
in (match (uu____6619) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____6624 = (FStar_List.tryFind (fun ps -> (FStar_Syntax_Syntax.fv_eq_lid fv ps.name)) cfg.primitive_steps)
in (match (uu____6624) with
| FStar_Pervasives_Native.None -> begin
tm
end
| FStar_Pervasives_Native.Some (prim_step) -> begin
(match (((FStar_List.length args) < prim_step.arity)) with
| true -> begin
tm
end
| uu____6636 -> begin
(

let uu____6637 = (prim_step.interpretation head1.FStar_Syntax_Syntax.pos args)
in (match (uu____6637) with
| FStar_Pervasives_Native.None -> begin
tm
end
| FStar_Pervasives_Native.Some (reduced) -> begin
reduced
end))
end)
end))
end
| uu____6641 -> begin
tm
end))
end))
end)))


let reduce_equality : cfg  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (reduce_primops (

let uu___176_6652 = cfg
in {steps = (Primops)::[]; tcenv = uu___176_6652.tcenv; delta_level = uu___176_6652.delta_level; primitive_steps = equality_ops}) tm))


let maybe_simplify : cfg  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (

let steps = cfg.steps
in (

let w = (fun t -> (

let uu___177_6676 = t
in {FStar_Syntax_Syntax.n = uu___177_6676.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___177_6676.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_Pervasives_Native.Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid) -> begin
FStar_Pervasives_Native.Some (false)
end
| uu____6693 -> begin
FStar_Pervasives_Native.None
end))
in (

let simplify = (fun arg -> (((simp_t (FStar_Pervasives_Native.fst arg))), (arg)))
in (

let tm1 = (reduce_primops cfg tm)
in (

let uu____6733 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps))
in (match (uu____6733) with
| true -> begin
tm1
end
| uu____6734 -> begin
(match (tm1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____6736; FStar_Syntax_Syntax.vars = uu____6737}, uu____6738); FStar_Syntax_Syntax.pos = uu____6739; FStar_Syntax_Syntax.vars = uu____6740}, args) -> begin
(

let uu____6766 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____6766) with
| true -> begin
(

let uu____6767 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____6767) with
| ((FStar_Pervasives_Native.Some (true), uu____6822))::((uu____6823, (arg, uu____6825)))::[] -> begin
arg
end
| ((uu____6890, (arg, uu____6892)))::((FStar_Pervasives_Native.Some (true), uu____6893))::[] -> begin
arg
end
| ((FStar_Pervasives_Native.Some (false), uu____6958))::(uu____6959)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____7022)::((FStar_Pervasives_Native.Some (false), uu____7023))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____7086 -> begin
tm1
end))
end
| uu____7101 -> begin
(

let uu____7102 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____7102) with
| true -> begin
(

let uu____7103 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____7103) with
| ((FStar_Pervasives_Native.Some (true), uu____7158))::(uu____7159)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____7222)::((FStar_Pervasives_Native.Some (true), uu____7223))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____7286))::((uu____7287, (arg, uu____7289)))::[] -> begin
arg
end
| ((uu____7354, (arg, uu____7356)))::((FStar_Pervasives_Native.Some (false), uu____7357))::[] -> begin
arg
end
| uu____7422 -> begin
tm1
end))
end
| uu____7437 -> begin
(

let uu____7438 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____7438) with
| true -> begin
(

let uu____7439 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____7439) with
| (uu____7494)::((FStar_Pervasives_Native.Some (true), uu____7495))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____7558))::(uu____7559)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____7622))::((uu____7623, (arg, uu____7625)))::[] -> begin
arg
end
| ((uu____7690, (p, uu____7692)))::((uu____7693, (q, uu____7695)))::[] -> begin
(

let uu____7760 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____7760) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____7761 -> begin
tm1
end))
end
| uu____7762 -> begin
tm1
end))
end
| uu____7777 -> begin
(

let uu____7778 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____7778) with
| true -> begin
(

let uu____7779 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____7779) with
| ((FStar_Pervasives_Native.Some (true), uu____7834))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____7873))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____7912 -> begin
tm1
end))
end
| uu____7927 -> begin
(

let uu____7928 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____7928) with
| true -> begin
(match (args) with
| ((t, uu____7930))::[] -> begin
(

let uu____7947 = (

let uu____7948 = (FStar_Syntax_Subst.compress t)
in uu____7948.FStar_Syntax_Syntax.n)
in (match (uu____7947) with
| FStar_Syntax_Syntax.Tm_abs ((uu____7951)::[], body, uu____7953) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____7980 -> begin
tm1
end)
end
| uu____7983 -> begin
tm1
end))
end
| ((uu____7984, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____7985))))::((t, uu____7987))::[] -> begin
(

let uu____8026 = (

let uu____8027 = (FStar_Syntax_Subst.compress t)
in uu____8027.FStar_Syntax_Syntax.n)
in (match (uu____8026) with
| FStar_Syntax_Syntax.Tm_abs ((uu____8030)::[], body, uu____8032) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____8059 -> begin
tm1
end)
end
| uu____8062 -> begin
tm1
end))
end
| uu____8063 -> begin
tm1
end)
end
| uu____8072 -> begin
(

let uu____8073 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____8073) with
| true -> begin
(match (args) with
| ((t, uu____8075))::[] -> begin
(

let uu____8092 = (

let uu____8093 = (FStar_Syntax_Subst.compress t)
in uu____8093.FStar_Syntax_Syntax.n)
in (match (uu____8092) with
| FStar_Syntax_Syntax.Tm_abs ((uu____8096)::[], body, uu____8098) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____8125 -> begin
tm1
end)
end
| uu____8128 -> begin
tm1
end))
end
| ((uu____8129, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____8130))))::((t, uu____8132))::[] -> begin
(

let uu____8171 = (

let uu____8172 = (FStar_Syntax_Subst.compress t)
in uu____8172.FStar_Syntax_Syntax.n)
in (match (uu____8171) with
| FStar_Syntax_Syntax.Tm_abs ((uu____8175)::[], body, uu____8177) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____8204 -> begin
tm1
end)
end
| uu____8207 -> begin
tm1
end))
end
| uu____8208 -> begin
tm1
end)
end
| uu____8217 -> begin
(reduce_equality cfg tm1)
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8219; FStar_Syntax_Syntax.vars = uu____8220}, args) -> begin
(

let uu____8242 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____8242) with
| true -> begin
(

let uu____8243 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____8243) with
| ((FStar_Pervasives_Native.Some (true), uu____8298))::((uu____8299, (arg, uu____8301)))::[] -> begin
arg
end
| ((uu____8366, (arg, uu____8368)))::((FStar_Pervasives_Native.Some (true), uu____8369))::[] -> begin
arg
end
| ((FStar_Pervasives_Native.Some (false), uu____8434))::(uu____8435)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____8498)::((FStar_Pervasives_Native.Some (false), uu____8499))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____8562 -> begin
tm1
end))
end
| uu____8577 -> begin
(

let uu____8578 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____8578) with
| true -> begin
(

let uu____8579 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____8579) with
| ((FStar_Pervasives_Native.Some (true), uu____8634))::(uu____8635)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____8698)::((FStar_Pervasives_Native.Some (true), uu____8699))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____8762))::((uu____8763, (arg, uu____8765)))::[] -> begin
arg
end
| ((uu____8830, (arg, uu____8832)))::((FStar_Pervasives_Native.Some (false), uu____8833))::[] -> begin
arg
end
| uu____8898 -> begin
tm1
end))
end
| uu____8913 -> begin
(

let uu____8914 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____8914) with
| true -> begin
(

let uu____8915 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____8915) with
| (uu____8970)::((FStar_Pervasives_Native.Some (true), uu____8971))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____9034))::(uu____9035)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____9098))::((uu____9099, (arg, uu____9101)))::[] -> begin
arg
end
| ((uu____9166, (p, uu____9168)))::((uu____9169, (q, uu____9171)))::[] -> begin
(

let uu____9236 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____9236) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____9237 -> begin
tm1
end))
end
| uu____9238 -> begin
tm1
end))
end
| uu____9253 -> begin
(

let uu____9254 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____9254) with
| true -> begin
(

let uu____9255 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____9255) with
| ((FStar_Pervasives_Native.Some (true), uu____9310))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____9349))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____9388 -> begin
tm1
end))
end
| uu____9403 -> begin
(

let uu____9404 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____9404) with
| true -> begin
(match (args) with
| ((t, uu____9406))::[] -> begin
(

let uu____9423 = (

let uu____9424 = (FStar_Syntax_Subst.compress t)
in uu____9424.FStar_Syntax_Syntax.n)
in (match (uu____9423) with
| FStar_Syntax_Syntax.Tm_abs ((uu____9427)::[], body, uu____9429) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____9456 -> begin
tm1
end)
end
| uu____9459 -> begin
tm1
end))
end
| ((uu____9460, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____9461))))::((t, uu____9463))::[] -> begin
(

let uu____9502 = (

let uu____9503 = (FStar_Syntax_Subst.compress t)
in uu____9503.FStar_Syntax_Syntax.n)
in (match (uu____9502) with
| FStar_Syntax_Syntax.Tm_abs ((uu____9506)::[], body, uu____9508) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____9535 -> begin
tm1
end)
end
| uu____9538 -> begin
tm1
end))
end
| uu____9539 -> begin
tm1
end)
end
| uu____9548 -> begin
(

let uu____9549 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____9549) with
| true -> begin
(match (args) with
| ((t, uu____9551))::[] -> begin
(

let uu____9568 = (

let uu____9569 = (FStar_Syntax_Subst.compress t)
in uu____9569.FStar_Syntax_Syntax.n)
in (match (uu____9568) with
| FStar_Syntax_Syntax.Tm_abs ((uu____9572)::[], body, uu____9574) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____9601 -> begin
tm1
end)
end
| uu____9604 -> begin
tm1
end))
end
| ((uu____9605, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____9606))))::((t, uu____9608))::[] -> begin
(

let uu____9647 = (

let uu____9648 = (FStar_Syntax_Subst.compress t)
in uu____9648.FStar_Syntax_Syntax.n)
in (match (uu____9647) with
| FStar_Syntax_Syntax.Tm_abs ((uu____9651)::[], body, uu____9653) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____9680 -> begin
tm1
end)
end
| uu____9683 -> begin
tm1
end))
end
| uu____9684 -> begin
tm1
end)
end
| uu____9693 -> begin
(reduce_equality cfg tm1)
end))
end))
end))
end))
end))
end))
end
| uu____9694 -> begin
tm1
end)
end))))))))


let is_norm_request : 'Auu____9701 . FStar_Syntax_Syntax.term  ->  'Auu____9701 Prims.list  ->  Prims.bool = (fun hd1 args -> (

let uu____9714 = (

let uu____9721 = (

let uu____9722 = (FStar_Syntax_Util.un_uinst hd1)
in uu____9722.FStar_Syntax_Syntax.n)
in ((uu____9721), (args)))
in (match (uu____9714) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____9728)::(uu____9729)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____9733)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (steps)::(uu____9738)::(uu____9739)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm)
end
| uu____9742 -> begin
false
end)))


let get_norm_request : 'Auu____9755 . (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term * 'Auu____9755) Prims.list  ->  (step Prims.list * FStar_Syntax_Syntax.term) = (fun full_norm args -> (

let parse_steps = (fun s -> (

let unembed_step = (fun s1 -> (

let uu____9797 = (

let uu____9798 = (FStar_Syntax_Util.un_uinst s1)
in uu____9798.FStar_Syntax_Syntax.n)
in (match (uu____9797) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta) -> begin
Zeta
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota) -> begin
Iota
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops) -> begin
Primops
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta) -> begin
UnfoldUntil (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta_only) -> begin
UnfoldUntil (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____9807; FStar_Syntax_Syntax.vars = uu____9808}, ((names1, uu____9810))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta_only) -> begin
(

let names2 = (FStar_Syntax_Embeddings.unembed_string_list names1)
in (

let lids = (FStar_All.pipe_right names2 (FStar_List.map FStar_Ident.lid_of_str))
in UnfoldOnly (lids)))
end
| uu____9849 -> begin
(failwith "Not an embedded `Prims.step`")
end)))
in (FStar_Syntax_Embeddings.unembed_list unembed_step s)))
in (match (args) with
| (uu____9856)::((tm, uu____9858))::[] -> begin
(

let s = (Beta)::(Zeta)::(Iota)::(Primops)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Reify)::[]
in ((s), (tm)))
end
| ((tm, uu____9881))::[] -> begin
(

let s = (Beta)::(Zeta)::(Iota)::(Primops)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Reify)::[]
in ((s), (tm)))
end
| ((steps, uu____9896))::(uu____9897)::((tm, uu____9899))::[] -> begin
(

let add_exclude = (fun s z -> (match ((not ((FStar_List.contains z s)))) with
| true -> begin
(Exclude (z))::s
end
| uu____9935 -> begin
s
end))
in (

let s = (

let uu____9939 = (

let uu____9942 = (full_norm steps)
in (parse_steps uu____9942))
in (Beta)::uu____9939)
in (

let s1 = (add_exclude s Zeta)
in (

let s2 = (add_exclude s1 Iota)
in ((s2), (tm))))))
end
| uu____9951 -> begin
(failwith "Impossible")
end)))


let is_reify_head : stack_elt Prims.list  ->  Prims.bool = (fun uu___146_9969 -> (match (uu___146_9969) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____9972; FStar_Syntax_Syntax.vars = uu____9973}, uu____9974, uu____9975))::uu____9976 -> begin
true
end
| uu____9983 -> begin
false
end))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let firstn = (fun k l -> (match (((FStar_List.length l) < k)) with
| true -> begin
((l), ([]))
end
| uu____10112 -> begin
(FStar_Util.first_N k l)
end))
in ((log cfg (fun uu____10118 -> (

let uu____10119 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____10120 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10121 = (

let uu____10122 = (

let uu____10125 = (firstn (Prims.parse_int "4") stack1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10125))
in (stack_to_string uu____10122))
in (FStar_Util.print3 ">>> %s\nNorm %s with top of the stack %s \n" uu____10119 uu____10120 uu____10121))))));
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____10148) -> begin
(failwith "Impossible: got a delayed substitution")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____10173) when (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars)) -> begin
(

let uu____10190 = (

let uu____10191 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____10192 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s) CheckNoUvars: Unexpected unification variable remains: %s" uu____10191 uu____10192)))
in (failwith uu____10190))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____10193) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_constant (uu____10210) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____10211) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10212; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = uu____10213}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10216; FStar_Syntax_Syntax.fv_delta = uu____10217; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10218; FStar_Syntax_Syntax.fv_delta = uu____10219; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____10220))}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)) -> begin
(

let args1 = (closures_as_args_delayed cfg env args)
in (

let hd2 = (closure_as_term cfg env hd1)
in (

let t2 = (

let uu___178_10262 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd2), (args1))); FStar_Syntax_Syntax.pos = uu___178_10262.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___178_10262.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack1 t2))))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when (((

let uu____10295 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoFullNorm))
in (not (uu____10295))) && (is_norm_request hd1 args)) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid)))) -> begin
(

let uu____10302 = (get_norm_request (norm (

let uu___179_10311 = cfg
in {steps = uu___179_10311.steps; tcenv = uu___179_10311.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]; primitive_steps = uu___179_10311.primitive_steps}) env []) args)
in (match (uu____10302) with
| (s, tm) -> begin
(

let delta_level = (

let uu____10321 = (FStar_All.pipe_right s (FStar_Util.for_some (fun uu___147_10326 -> (match (uu___147_10326) with
| UnfoldUntil (uu____10327) -> begin
true
end
| UnfoldOnly (uu____10328) -> begin
true
end
| uu____10331 -> begin
false
end))))
in (match (uu____10321) with
| true -> begin
(FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]
end
| uu____10334 -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end))
in (

let cfg' = (

let uu___180_10336 = cfg
in {steps = s; tcenv = uu___180_10336.tcenv; delta_level = delta_level; primitive_steps = uu___180_10336.primitive_steps})
in (

let stack' = (Debug (t1))::(Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (norm cfg' env stack' tm))))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____10344; FStar_Syntax_Syntax.vars = uu____10345}, (a1)::(a2)::rest) -> begin
(

let uu____10393 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____10393) with
| (hd1, uu____10409) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), ((a1)::[])))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (norm cfg env stack1 t2)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____10474)); FStar_Syntax_Syntax.pos = uu____10475; FStar_Syntax_Syntax.vars = uu____10476}, (a)::[]) when ((FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) && (is_reify_head stack1)) -> begin
(

let uu____10508 = (FStar_List.tl stack1)
in (norm cfg env uu____10508 (FStar_Pervasives_Native.fst a)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____10511; FStar_Syntax_Syntax.vars = uu____10512}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let uu____10544 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____10544) with
| (reify_head, uu____10560) -> begin
(

let a1 = (

let uu____10582 = (FStar_All.pipe_left FStar_Syntax_Util.unascribe (FStar_Pervasives_Native.fst a))
in (FStar_Syntax_Subst.compress uu____10582))
in (match (a1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____10585)); FStar_Syntax_Syntax.pos = uu____10586; FStar_Syntax_Syntax.vars = uu____10587}, (a2)::[]) -> begin
(norm cfg env stack1 (FStar_Pervasives_Native.fst a2))
end
| uu____10621 -> begin
(

let stack2 = (App (((reify_head), (FStar_Pervasives_Native.None), (t1.FStar_Syntax_Syntax.pos))))::stack1
in (norm cfg env stack2 a1))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u1 = (norm_universe cfg env u)
in (

let uu____10631 = (mk (FStar_Syntax_Syntax.Tm_type (u1)) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 uu____10631)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let uu____10638 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____10638) with
| true -> begin
(norm cfg env stack1 t')
end
| uu____10639 -> begin
(

let us1 = (

let uu____10641 = (

let uu____10648 = (FStar_List.map (norm_universe cfg env) us)
in ((uu____10648), (t1.FStar_Syntax_Syntax.pos)))
in UnivArgs (uu____10641))
in (

let stack2 = (us1)::stack1
in (norm cfg env stack2 t')))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t1
in (

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun uu___148_10662 -> (match (uu___148_10662) with
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

let uu____10665 = ((FStar_List.mem FStar_TypeChecker_Env.UnfoldTac cfg.delta_level) && (((((((((FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.and_lid) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.imp_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.forall_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.exists_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.eq2_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.true_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.false_lid)))
in (match (uu____10665) with
| true -> begin
false
end
| uu____10666 -> begin
(

let uu____10667 = (FStar_All.pipe_right cfg.steps (FStar_List.tryFind (fun uu___149_10674 -> (match (uu___149_10674) with
| UnfoldOnly (uu____10675) -> begin
true
end
| uu____10678 -> begin
false
end))))
in (match (uu____10667) with
| FStar_Pervasives_Native.Some (UnfoldOnly (lids)) -> begin
(should_delta && (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid f) lids))
end
| uu____10682 -> begin
should_delta
end))
end))
in (match ((not (should_delta1))) with
| true -> begin
(rebuild cfg env stack1 t1)
end
| uu____10685 -> begin
(

let r_env = (

let uu____10687 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv uu____10687))
in (

let uu____10688 = (FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10688) with
| FStar_Pervasives_Native.None -> begin
((log cfg (fun uu____10701 -> (FStar_Util.print "Tm_fvar case 2\n" [])));
(rebuild cfg env stack1 t1);
)
end
| FStar_Pervasives_Native.Some (us, t2) -> begin
((log cfg (fun uu____10712 -> (

let uu____10713 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____10714 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____10713 uu____10714)))));
(

let t3 = (

let uu____10716 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))))
in (match (uu____10716) with
| true -> begin
t2
end
| uu____10717 -> begin
(FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) t2)
end))
in (

let n1 = (FStar_List.length us)
in (match ((n1 > (Prims.parse_int "0"))) with
| true -> begin
(match (stack1) with
| (UnivArgs (us', uu____10726))::stack2 -> begin
(

let env1 = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env1 u -> (Univ (u))::env1) env))
in (norm cfg env1 stack2 t3))
end
| uu____10749 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack1 t3)
end
| uu____10750 -> begin
(

let uu____10751 = (

let uu____10752 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" uu____10752))
in (failwith uu____10751))
end)
end
| uu____10753 -> begin
(norm cfg env stack1 t3)
end)));
)
end)))
end))))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____10755 = (lookup_bvar env x)
in (match (uu____10755) with
| Univ (uu____10756) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env1, t0, r, fix) -> begin
(match (((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps))))) with
| true -> begin
(

let uu____10781 = (FStar_ST.read r)
in (match (uu____10781) with
| FStar_Pervasives_Native.Some (env2, t') -> begin
((log cfg (fun uu____10816 -> (

let uu____10817 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10818 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" uu____10817 uu____10818)))));
(

let uu____10819 = (

let uu____10820 = (FStar_Syntax_Subst.compress t')
in uu____10820.FStar_Syntax_Syntax.n)
in (match (uu____10819) with
| FStar_Syntax_Syntax.Tm_abs (uu____10823) -> begin
(norm cfg env2 stack1 t')
end
| uu____10840 -> begin
(rebuild cfg env2 stack1 t')
end));
)
end
| FStar_Pervasives_Native.None -> begin
(norm cfg env1 ((MemoLazy (r))::stack1) t0)
end))
end
| uu____10850 -> begin
(norm cfg env1 stack1 t0)
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack1) with
| (UnivArgs (uu____10874))::uu____10875 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (uu____10884))::uu____10885 -> begin
(failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, uu____10895, uu____10896))::stack_rest -> begin
(match (c) with
| Univ (uu____10900) -> begin
(norm cfg ((c)::env) stack_rest t1)
end
| uu____10901 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (uu____10906)::[] -> begin
(match (lopt) with
| FStar_Pervasives_Native.None when (FStar_Options.__unit_tests ()) -> begin
((log cfg (fun uu____10922 -> (

let uu____10923 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____10923))));
(norm cfg ((c)::env) stack_rest body);
)
end
| FStar_Pervasives_Native.Some (rc) when (((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) || (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_Util.for_some (fun uu___150_10928 -> (match (uu___150_10928) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____10929 -> begin
false
end))))) -> begin
((log cfg (fun uu____10933 -> (

let uu____10934 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____10934))));
(norm cfg ((c)::env) stack_rest body);
)
end
| uu____10935 when ((FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) || (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| uu____10938 -> begin
(

let cfg1 = (

let uu___181_10942 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = uu___181_10942.tcenv; delta_level = uu___181_10942.delta_level; primitive_steps = uu___181_10942.primitive_steps})
in (

let uu____10943 = (closure_as_term cfg1 env t1)
in (rebuild cfg1 env stack1 uu____10943)))
end)
end
| (uu____10944)::tl1 -> begin
((log cfg (fun uu____10963 -> (

let uu____10964 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____10964))));
(

let body1 = (mk (FStar_Syntax_Syntax.Tm_abs (((tl1), (body), (lopt)))) t1.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body1));
)
end)
end)
end
| (Steps (s, ps, dl))::stack2 -> begin
(norm (

let uu___182_10994 = cfg
in {steps = s; tcenv = uu___182_10994.tcenv; delta_level = dl; primitive_steps = ps}) env stack2 t1)
end
| (MemoLazy (r))::stack2 -> begin
((set_memo r ((env), (t1)));
(log cfg (fun uu____11015 -> (

let uu____11016 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____11016))));
(norm cfg env stack2 t1);
)
end
| (Debug (uu____11017))::uu____11018 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____11021 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____11021))
end
| uu____11022 -> begin
(

let uu____11023 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11023) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11047 -> (Dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____11063 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____11063) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11073 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11073))))
end
| uu____11074 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___183_11078 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___183_11078.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___183_11078.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11079 -> begin
lopt
end)
in ((log cfg (fun uu____11085 -> (

let uu____11086 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11086))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___184_11099 = cfg
in (

let uu____11100 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___184_11099.steps; tcenv = uu___184_11099.tcenv; delta_level = uu___184_11099.delta_level; primitive_steps = uu____11100}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Meta (uu____11109))::uu____11110 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____11117 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____11117))
end
| uu____11118 -> begin
(

let uu____11119 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11119) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11143 -> (Dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____11159 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____11159) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11169 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11169))))
end
| uu____11170 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___183_11174 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___183_11174.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___183_11174.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11175 -> begin
lopt
end)
in ((log cfg (fun uu____11181 -> (

let uu____11182 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11182))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___184_11195 = cfg
in (

let uu____11196 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___184_11195.steps; tcenv = uu___184_11195.tcenv; delta_level = uu___184_11195.delta_level; primitive_steps = uu____11196}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Let (uu____11205))::uu____11206 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____11217 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____11217))
end
| uu____11218 -> begin
(

let uu____11219 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11219) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11243 -> (Dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____11259 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____11259) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11269 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11269))))
end
| uu____11270 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___183_11274 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___183_11274.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___183_11274.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11275 -> begin
lopt
end)
in ((log cfg (fun uu____11281 -> (

let uu____11282 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11282))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___184_11295 = cfg
in (

let uu____11296 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___184_11295.steps; tcenv = uu___184_11295.tcenv; delta_level = uu___184_11295.delta_level; primitive_steps = uu____11296}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (App (uu____11305))::uu____11306 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____11315 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____11315))
end
| uu____11316 -> begin
(

let uu____11317 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11317) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11341 -> (Dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____11357 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____11357) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11367 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11367))))
end
| uu____11368 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___183_11372 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___183_11372.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___183_11372.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11373 -> begin
lopt
end)
in ((log cfg (fun uu____11379 -> (

let uu____11380 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11380))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___184_11393 = cfg
in (

let uu____11394 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___184_11393.steps; tcenv = uu___184_11393.tcenv; delta_level = uu___184_11393.delta_level; primitive_steps = uu____11394}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Abs (uu____11403))::uu____11404 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____11419 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____11419))
end
| uu____11420 -> begin
(

let uu____11421 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11421) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11445 -> (Dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____11461 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____11461) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11471 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11471))))
end
| uu____11472 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___183_11476 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___183_11476.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___183_11476.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11477 -> begin
lopt
end)
in ((log cfg (fun uu____11483 -> (

let uu____11484 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11484))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___184_11497 = cfg
in (

let uu____11498 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___184_11497.steps; tcenv = uu___184_11497.tcenv; delta_level = uu___184_11497.delta_level; primitive_steps = uu____11498}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| [] -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____11507 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____11507))
end
| uu____11508 -> begin
(

let uu____11509 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11509) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11533 -> (Dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____11549 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____11549) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11559 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11559))))
end
| uu____11560 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___183_11564 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___183_11564.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___183_11564.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11565 -> begin
lopt
end)
in ((log cfg (fun uu____11571 -> (

let uu____11572 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11572))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___184_11585 = cfg
in (

let uu____11586 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___184_11585.steps; tcenv = uu___184_11585.tcenv; delta_level = uu___184_11585.delta_level; primitive_steps = uu____11586}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack2 = (FStar_All.pipe_right stack1 (FStar_List.fold_right (fun uu____11633 stack2 -> (match (uu____11633) with
| (a, aq) -> begin
(

let uu____11645 = (

let uu____11646 = (

let uu____11653 = (

let uu____11654 = (

let uu____11673 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____11673), (false)))
in Clos (uu____11654))
in ((uu____11653), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____11646))
in (uu____11645)::stack2)
end)) args))
in ((log cfg (fun uu____11713 -> (

let uu____11714 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____11714))));
(norm cfg env stack2 head1);
))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(match (((env), (stack1))) with
| ([], []) -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let t2 = (mk (FStar_Syntax_Syntax.Tm_refine ((((

let uu___185_11738 = x
in {FStar_Syntax_Syntax.ppname = uu___185_11738.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___185_11738.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 t2)))
end
| uu____11739 -> begin
(

let uu____11744 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____11744))
end)
end
| uu____11745 -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let uu____11747 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____11747) with
| (closing, f1) -> begin
(

let f2 = (norm cfg ((Dummy)::env) [] f1)
in (

let t2 = (

let uu____11772 = (

let uu____11773 = (

let uu____11780 = (FStar_Syntax_Subst.close closing f2)
in (((

let uu___186_11782 = x
in {FStar_Syntax_Syntax.ppname = uu___186_11782.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___186_11782.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (uu____11780)))
in FStar_Syntax_Syntax.Tm_refine (uu____11773))
in (mk uu____11772 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack1 t2)))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____11801 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____11801))
end
| uu____11802 -> begin
(

let uu____11803 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____11803) with
| (bs1, c1) -> begin
(

let c2 = (

let uu____11811 = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11823 -> (Dummy)::env1) env))
in (norm_comp cfg uu____11811 c1))
in (

let t2 = (

let uu____11833 = (norm_binders cfg env bs1)
in (FStar_Syntax_Util.arrow uu____11833 c2))
in (rebuild cfg env stack1 t2)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) -> begin
(match (stack1) with
| (Match (uu____11892))::uu____11893 -> begin
(norm cfg env stack1 t11)
end
| (Arg (uu____11902))::uu____11903 -> begin
(norm cfg env stack1 t11)
end
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____11912; FStar_Syntax_Syntax.vars = uu____11913}, uu____11914, uu____11915))::uu____11916 -> begin
(norm cfg env stack1 t11)
end
| (MemoLazy (uu____11923))::uu____11924 -> begin
(norm cfg env stack1 t11)
end
| uu____11933 -> begin
(

let t12 = (norm cfg env [] t11)
in ((log cfg (fun uu____11937 -> (FStar_Util.print_string "+++ Normalizing ascription \n")));
(

let tc1 = (match (tc) with
| FStar_Util.Inl (t2) -> begin
(

let uu____11954 = (norm cfg env [] t2)
in FStar_Util.Inl (uu____11954))
end
| FStar_Util.Inr (c) -> begin
(

let uu____11962 = (norm_comp cfg env c)
in FStar_Util.Inr (uu____11962))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (norm cfg env []))
in (

let uu____11968 = (

let uu____11969 = (

let uu____11970 = (

let uu____11997 = (FStar_Syntax_Util.unascribe t12)
in ((uu____11997), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____11970))
in (mk uu____11969 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack1 uu____11968))));
))
end)
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let stack2 = (Match (((env), (branches), (t1.FStar_Syntax_Syntax.pos))))::stack1
in (norm cfg env stack2 head1))
end
| FStar_Syntax_Syntax.Tm_let ((uu____12073, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____12074); FStar_Syntax_Syntax.lbunivs = uu____12075; FStar_Syntax_Syntax.lbtyp = uu____12076; FStar_Syntax_Syntax.lbeff = uu____12077; FStar_Syntax_Syntax.lbdef = uu____12078})::uu____12079), uu____12080) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n1 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in (

let uu____12116 = ((

let uu____12119 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps))
in (not (uu____12119))) && ((FStar_Syntax_Util.is_pure_effect n1) || ((FStar_Syntax_Util.is_ghost_effect n1) && (

let uu____12121 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (not (uu____12121))))))
in (match (uu____12116) with
| true -> begin
(

let env1 = (

let uu____12125 = (

let uu____12126 = (

let uu____12145 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (uu____12145), (false)))
in Clos (uu____12126))
in (uu____12125)::env)
in (norm cfg env1 stack1 body))
end
| uu____12184 -> begin
(

let uu____12185 = (

let uu____12190 = (

let uu____12191 = (

let uu____12192 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right uu____12192 FStar_Syntax_Syntax.mk_binder))
in (uu____12191)::[])
in (FStar_Syntax_Subst.open_term uu____12190 body))
in (match (uu____12185) with
| (bs, body1) -> begin
(

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let x = (

let uu____12206 = (FStar_List.hd bs)
in (FStar_Pervasives_Native.fst uu____12206))
in FStar_Util.Inl ((

let uu___187_12216 = x
in {FStar_Syntax_Syntax.ppname = uu___187_12216.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___187_12216.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
in (

let lb1 = (

let uu___188_12218 = lb
in (

let uu____12219 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___188_12218.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___188_12218.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____12219}))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env1 uu____12236 -> (Dummy)::env1) env))
in (norm cfg env' ((Let (((env), (bs), (lb1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), body) when (FStar_List.contains CompressUvars cfg.steps) -> begin
(

let uu____12259 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____12259) with
| (lbs1, body1) -> begin
(

let lbs2 = (FStar_List.map (fun lb -> (

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let uu____12295 = (

let uu___189_12296 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___189_12296.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___189_12296.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})
in FStar_Util.Inl (uu____12295))
in (

let uu____12297 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____12297) with
| (xs, def_body, lopt) -> begin
(

let xs1 = (norm_binders cfg env xs)
in (

let env1 = (

let uu____12317 = (FStar_List.map (fun uu____12321 -> Dummy) lbs1)
in (

let uu____12322 = (

let uu____12325 = (FStar_List.map (fun uu____12333 -> Dummy) xs1)
in (FStar_List.append uu____12325 env))
in (FStar_List.append uu____12317 uu____12322)))
in (

let def_body1 = (norm cfg env1 [] def_body)
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____12345 = (

let uu___190_12346 = rc
in (

let uu____12347 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env1 []))
in {FStar_Syntax_Syntax.residual_effect = uu___190_12346.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____12347; FStar_Syntax_Syntax.residual_flags = uu___190_12346.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____12345))
end
| uu____12354 -> begin
lopt
end)
in (

let def = (FStar_Syntax_Util.abs xs1 def_body1 lopt1)
in (

let uu___191_12358 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___191_12358.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___191_12358.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def}))))))
end))))) lbs1)
in (

let env' = (

let uu____12362 = (FStar_List.map (fun uu____12366 -> Dummy) lbs2)
in (FStar_List.append uu____12362 env))
in (

let body2 = (norm cfg env' [] body1)
in (

let uu____12368 = (FStar_Syntax_Subst.close_let_rec lbs2 body2)
in (match (uu____12368) with
| (lbs3, body3) -> begin
(

let t2 = (

let uu___192_12384 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (body3))); FStar_Syntax_Syntax.pos = uu___192_12384.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___192_12384.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack1 t2))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(

let uu____12411 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____12411))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let uu____12430 = (FStar_List.fold_right (fun lb uu____12481 -> (match (uu____12481) with
| (rec_env, memos, i) -> begin
(

let f_i = (

let uu____12554 = (

let uu___193_12555 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___193_12555.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___193_12555.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm uu____12554))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t1.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let rec_env1 = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env1), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (FStar_Pervasives_Native.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (uu____12430) with
| (rec_env, memos, uu____12659) -> begin
(

let uu____12688 = (FStar_List.map2 (fun lb memo -> (FStar_ST.write memo (FStar_Pervasives_Native.Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (FStar_Pervasives_Native.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env1 -> (

let uu____12758 = (

let uu____12759 = (

let uu____12778 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (uu____12778), (false)))
in Clos (uu____12759))
in (uu____12758)::env1)) (FStar_Pervasives_Native.snd lbs) env)
in (norm cfg body_env stack1 body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head1, m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m1, t2) -> begin
(

let should_reify = (match (stack1) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____12834; FStar_Syntax_Syntax.vars = uu____12835}, uu____12836, uu____12837))::uu____12838 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____12845 -> begin
false
end)
in (match ((not (should_reify))) with
| true -> begin
(

let t3 = (norm cfg env [] t2)
in (

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu____12855 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____12855) with
| true -> begin
(

let uu___194_12856 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::(NoDeltaSteps)::[]; tcenv = uu___194_12856.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___194_12856.primitive_steps})
end
| uu____12857 -> begin
(

let uu___195_12858 = cfg
in {steps = (FStar_List.append ((NoDeltaSteps)::(Exclude (Zeta))::[]) cfg.steps); tcenv = uu___195_12858.tcenv; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___195_12858.primitive_steps})
end))
in (norm cfg1 env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m1), (t3)))), (t3.FStar_Syntax_Syntax.pos))))::stack2) head1))))
end
| uu____12859 -> begin
(

let uu____12860 = (

let uu____12861 = (FStar_Syntax_Subst.compress head1)
in uu____12861.FStar_Syntax_Syntax.n)
in (match (uu____12860) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m1)
in (

let uu____12879 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____12879) with
| (uu____12880, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____12886) -> begin
(failwith "Cannot reify a top-level let binding")
end
| FStar_Util.Inl (x) -> begin
(

let is_return = (fun e -> (

let uu____12894 = (

let uu____12895 = (FStar_Syntax_Subst.compress e)
in uu____12895.FStar_Syntax_Syntax.n)
in (match (uu____12894) with
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____12901, uu____12902)) -> begin
(

let uu____12911 = (

let uu____12912 = (FStar_Syntax_Subst.compress e1)
in uu____12912.FStar_Syntax_Syntax.n)
in (match (uu____12911) with
| FStar_Syntax_Syntax.Tm_meta (e2, FStar_Syntax_Syntax.Meta_monadic_lift (uu____12918, msrc, uu____12920)) when (FStar_Syntax_Util.is_pure_effect msrc) -> begin
(

let uu____12929 = (FStar_Syntax_Subst.compress e2)
in FStar_Pervasives_Native.Some (uu____12929))
end
| uu____12930 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____12931 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____12932 = (is_return lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____12932) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let lb1 = (

let uu___196_12937 = lb
in {FStar_Syntax_Syntax.lbname = uu___196_12937.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___196_12937.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___196_12937.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = e})
in (

let uu____12938 = (FStar_List.tl stack1)
in (

let uu____12939 = (

let uu____12940 = (

let uu____12943 = (

let uu____12944 = (

let uu____12957 = (FStar_Syntax_Util.mk_reify body)
in ((((false), ((lb1)::[]))), (uu____12957)))
in FStar_Syntax_Syntax.Tm_let (uu____12944))
in (FStar_Syntax_Syntax.mk uu____12943))
in (uu____12940 FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos))
in (norm cfg env uu____12938 uu____12939))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____12973 = (

let uu____12974 = (is_return body)
in (match (uu____12974) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_bvar (y); FStar_Syntax_Syntax.pos = uu____12978; FStar_Syntax_Syntax.vars = uu____12979}) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____12984 -> begin
false
end))
in (match (uu____12973) with
| true -> begin
(norm cfg env stack1 lb.FStar_Syntax_Syntax.lbdef)
end
| uu____12987 -> begin
(

let head2 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body1 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify body)
in (

let body_rc = {FStar_Syntax_Syntax.residual_effect = m1; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t2); FStar_Syntax_Syntax.residual_flags = []}
in (

let body2 = (

let uu____13008 = (

let uu____13011 = (

let uu____13012 = (

let uu____13029 = (

let uu____13032 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____13032)::[])
in ((uu____13029), (body1), (FStar_Pervasives_Native.Some (body_rc))))
in FStar_Syntax_Syntax.Tm_abs (uu____13012))
in (FStar_Syntax_Syntax.mk uu____13011))
in (uu____13008 FStar_Pervasives_Native.None body1.FStar_Syntax_Syntax.pos))
in (

let close1 = (closure_as_term cfg env)
in (

let bind_inst = (

let uu____13048 = (

let uu____13049 = (FStar_Syntax_Subst.compress bind_repr)
in uu____13049.FStar_Syntax_Syntax.n)
in (match (uu____13048) with
| FStar_Syntax_Syntax.Tm_uinst (bind1, (uu____13055)::(uu____13056)::[]) -> begin
(

let uu____13063 = (

let uu____13066 = (

let uu____13067 = (

let uu____13074 = (

let uu____13077 = (

let uu____13078 = (close1 lb.FStar_Syntax_Syntax.lbtyp)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____13078))
in (

let uu____13079 = (

let uu____13082 = (

let uu____13083 = (close1 t2)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____13083))
in (uu____13082)::[])
in (uu____13077)::uu____13079))
in ((bind1), (uu____13074)))
in FStar_Syntax_Syntax.Tm_uinst (uu____13067))
in (FStar_Syntax_Syntax.mk uu____13066))
in (uu____13063 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
end
| uu____13091 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let reified = (

let uu____13097 = (

let uu____13100 = (

let uu____13101 = (

let uu____13116 = (

let uu____13119 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____13120 = (

let uu____13123 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____13124 = (

let uu____13127 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____13128 = (

let uu____13131 = (FStar_Syntax_Syntax.as_arg head2)
in (

let uu____13132 = (

let uu____13135 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____13136 = (

let uu____13139 = (FStar_Syntax_Syntax.as_arg body2)
in (uu____13139)::[])
in (uu____13135)::uu____13136))
in (uu____13131)::uu____13132))
in (uu____13127)::uu____13128))
in (uu____13123)::uu____13124))
in (uu____13119)::uu____13120))
in ((bind_inst), (uu____13116)))
in FStar_Syntax_Syntax.Tm_app (uu____13101))
in (FStar_Syntax_Syntax.mk uu____13100))
in (uu____13097 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (

let uu____13147 = (FStar_List.tl stack1)
in (norm cfg env uu____13147 reified)))))))))
end))
end)))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head_app, args) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m1)
in (

let uu____13171 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____13171) with
| (uu____13172, bind_repr) -> begin
(

let maybe_unfold_action = (fun head2 -> (

let maybe_extract_fv = (fun t3 -> (

let t4 = (

let uu____13201 = (

let uu____13202 = (FStar_Syntax_Subst.compress t3)
in uu____13202.FStar_Syntax_Syntax.n)
in (match (uu____13201) with
| FStar_Syntax_Syntax.Tm_uinst (t4, uu____13208) -> begin
t4
end
| uu____13213 -> begin
head2
end))
in (

let uu____13214 = (

let uu____13215 = (FStar_Syntax_Subst.compress t4)
in uu____13215.FStar_Syntax_Syntax.n)
in (match (uu____13214) with
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____13221 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____13222 = (maybe_extract_fv head2)
in (match (uu____13222) with
| FStar_Pervasives_Native.Some (x) when (

let uu____13232 = (FStar_Syntax_Syntax.lid_of_fv x)
in (FStar_TypeChecker_Env.is_action cfg.tcenv uu____13232)) -> begin
(

let head3 = (norm cfg env [] head2)
in (

let action_unfolded = (

let uu____13237 = (maybe_extract_fv head3)
in (match (uu____13237) with
| FStar_Pervasives_Native.Some (uu____13242) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____13243 -> begin
FStar_Pervasives_Native.Some (false)
end))
in ((head3), (action_unfolded))))
end
| uu____13248 -> begin
((head2), (FStar_Pervasives_Native.None))
end))))
in ((

let is_arg_impure = (fun uu____13263 -> (match (uu____13263) with
| (e, q) -> begin
(

let uu____13270 = (

let uu____13271 = (FStar_Syntax_Subst.compress e)
in uu____13271.FStar_Syntax_Syntax.n)
in (match (uu____13270) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m11, m2, t')) -> begin
(not ((FStar_Syntax_Util.is_pure_effect m11)))
end
| uu____13286 -> begin
false
end))
end))
in (

let uu____13287 = (

let uu____13288 = (

let uu____13295 = (FStar_Syntax_Syntax.as_arg head_app)
in (uu____13295)::args)
in (FStar_Util.for_some is_arg_impure uu____13288))
in (match (uu____13287) with
| true -> begin
(

let uu____13300 = (

let uu____13301 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format1 "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n" uu____13301))
in (failwith uu____13300))
end
| uu____13302 -> begin
()
end)));
(

let uu____13303 = (maybe_unfold_action head_app)
in (match (uu____13303) with
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

let uu____13342 = (FStar_List.tl stack1)
in (norm cfg env uu____13342 body1)))))
end));
))
end)))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (

let uu____13356 = (closure_as_term cfg env t')
in (reify_lift cfg.tcenv e msrc mtgt uu____13356))
in (

let uu____13357 = (FStar_List.tl stack1)
in (norm cfg env uu____13357 lifted)))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____13478 -> (match (uu____13478) with
| (pat, wopt, tm) -> begin
(

let uu____13526 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____13526)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches1)))) t2.FStar_Syntax_Syntax.pos)
in (

let uu____13558 = (FStar_List.tl stack1)
in (norm cfg env uu____13558 tm))))
end
| uu____13559 -> begin
(norm cfg env stack1 head1)
end))
end))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) -> begin
(

let should_reify = (match (stack1) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____13568; FStar_Syntax_Syntax.vars = uu____13569}, uu____13570, uu____13571))::uu____13572 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____13579 -> begin
false
end)
in (match (should_reify) with
| true -> begin
(

let uu____13580 = (FStar_List.tl stack1)
in (

let uu____13581 = (

let uu____13582 = (closure_as_term cfg env t2)
in (reify_lift cfg.tcenv head1 m1 m' uu____13582))
in (norm cfg env uu____13580 uu____13581)))
end
| uu____13583 -> begin
(

let t3 = (norm cfg env [] t2)
in (

let uu____13585 = (((FStar_Syntax_Util.is_pure_effect m1) || (FStar_Syntax_Util.is_ghost_effect m1)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)))
in (match (uu____13585) with
| true -> begin
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___197_13594 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = uu___197_13594.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___197_13594.primitive_steps})
in (norm cfg1 env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t3)))), (head1.FStar_Syntax_Syntax.pos))))::stack2) head1)))
end
| uu____13595 -> begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t3)))), (head1.FStar_Syntax_Syntax.pos))))::stack1) head1)
end)))
end))
end
| uu____13596 -> begin
(match (stack1) with
| (uu____13597)::uu____13598 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____13603) -> begin
(norm cfg env ((Meta (((m), (r))))::stack1) head1)
end
| FStar_Syntax_Syntax.Meta_alien (b, s) -> begin
(norm cfg env ((Meta (((m), (t1.FStar_Syntax_Syntax.pos))))::stack1) head1)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args1 = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args1)), (t1.FStar_Syntax_Syntax.pos))))::stack1) head1))
end
| uu____13628 -> begin
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

let uu____13642 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (uu____13642))
end
| uu____13653 -> begin
m
end)
in (

let t2 = (mk (FStar_Syntax_Syntax.Tm_meta (((head2), (m1)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 t2))))
end)
end)
end);
))))
and reify_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env e msrc mtgt t -> (match ((FStar_Syntax_Util.is_pure_effect msrc)) with
| true -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl env mtgt)
in (

let uu____13665 = ed.FStar_Syntax_Syntax.return_repr
in (match (uu____13665) with
| (uu____13666, return_repr) -> begin
(

let return_inst = (

let uu____13675 = (

let uu____13676 = (FStar_Syntax_Subst.compress return_repr)
in uu____13676.FStar_Syntax_Syntax.n)
in (match (uu____13675) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (uu____13682)::[]) -> begin
(

let uu____13689 = (

let uu____13692 = (

let uu____13693 = (

let uu____13700 = (

let uu____13703 = (env.FStar_TypeChecker_Env.universe_of env t)
in (uu____13703)::[])
in ((return_tm), (uu____13700)))
in FStar_Syntax_Syntax.Tm_uinst (uu____13693))
in (FStar_Syntax_Syntax.mk uu____13692))
in (uu____13689 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end
| uu____13711 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let uu____13714 = (

let uu____13717 = (

let uu____13718 = (

let uu____13733 = (

let uu____13736 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____13737 = (

let uu____13740 = (FStar_Syntax_Syntax.as_arg e)
in (uu____13740)::[])
in (uu____13736)::uu____13737))
in ((return_inst), (uu____13733)))
in FStar_Syntax_Syntax.Tm_app (uu____13718))
in (FStar_Syntax_Syntax.mk uu____13717))
in (uu____13714 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end)))
end
| uu____13748 -> begin
(

let uu____13749 = (FStar_TypeChecker_Env.monad_leq env msrc mtgt)
in (match (uu____13749) with
| FStar_Pervasives_Native.None -> begin
(

let uu____13752 = (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" (FStar_Ident.text_of_lid msrc) (FStar_Ident.text_of_lid mtgt))
in (failwith uu____13752))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____13753; FStar_TypeChecker_Env.mtarget = uu____13754; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____13755; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(failwith "Impossible : trying to reify a non-reifiable lift (from %s to %s)")
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____13766; FStar_TypeChecker_Env.mtarget = uu____13767; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____13768; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let uu____13786 = (FStar_Syntax_Util.mk_reify e)
in (lift t FStar_Syntax_Syntax.tun uu____13786))
end))
end))
and norm_pattern_args : cfg  ->  env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun uu____13842 -> (match (uu____13842) with
| (a, imp) -> begin
(

let uu____13853 = (norm cfg env [] a)
in ((uu____13853), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp1 = (ghost_to_pure_aux cfg env comp)
in (match (comp1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu___198_13870 = comp1
in (

let uu____13873 = (

let uu____13874 = (

let uu____13883 = (norm cfg env [] t)
in (

let uu____13884 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____13883), (uu____13884))))
in FStar_Syntax_Syntax.Total (uu____13874))
in {FStar_Syntax_Syntax.n = uu____13873; FStar_Syntax_Syntax.pos = uu___198_13870.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___198_13870.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu___199_13899 = comp1
in (

let uu____13902 = (

let uu____13903 = (

let uu____13912 = (norm cfg env [] t)
in (

let uu____13913 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____13912), (uu____13913))))
in FStar_Syntax_Syntax.GTotal (uu____13903))
in {FStar_Syntax_Syntax.n = uu____13902; FStar_Syntax_Syntax.pos = uu___199_13899.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___199_13899.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____13965 -> (match (uu____13965) with
| (a, i) -> begin
(

let uu____13976 = (norm cfg env [] a)
in ((uu____13976), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___151_13987 -> (match (uu___151_13987) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____13991 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____13991))
end
| f -> begin
f
end))))
in (

let uu___200_13995 = comp1
in (

let uu____13998 = (

let uu____13999 = (

let uu___201_14000 = ct
in (

let uu____14001 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (

let uu____14002 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____14005 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = uu____14001; FStar_Syntax_Syntax.effect_name = uu___201_14000.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____14002; FStar_Syntax_Syntax.effect_args = uu____14005; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (uu____13999))
in {FStar_Syntax_Syntax.n = uu____13998; FStar_Syntax_Syntax.pos = uu___200_13995.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___200_13995.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm1 = (fun t -> (norm (

let uu___202_14023 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = uu___202_14023.tcenv; delta_level = uu___202_14023.delta_level; primitive_steps = uu___202_14023.primitive_steps}) env [] t))
in (

let non_info = (fun t -> (

let uu____14028 = (norm1 t)
in (FStar_Syntax_Util.non_informative uu____14028)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____14031) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let uu___203_14050 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.pos = uu___203_14050.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___203_14050.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____14057 = ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ))
in (match (uu____14057) with
| true -> begin
(

let ct1 = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let flags = (match ((FStar_Ident.lid_equals pure_eff FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::ct.FStar_Syntax_Syntax.flags
end
| uu____14067 -> begin
ct.FStar_Syntax_Syntax.flags
end)
in (

let uu___204_14068 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___204_14068.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = uu___204_14068.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___204_14068.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags}))
end
| FStar_Pervasives_Native.None -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c)
in (

let uu___205_14070 = ct1
in {FStar_Syntax_Syntax.comp_univs = uu___205_14070.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu___205_14070.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___205_14070.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___205_14070.FStar_Syntax_Syntax.flags}))
end)
in (

let uu___206_14071 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___206_14071.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___206_14071.FStar_Syntax_Syntax.vars}))
end
| uu____14072 -> begin
c
end)))
end
| uu____14073 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env uu____14076 -> (match (uu____14076) with
| (x, imp) -> begin
(

let uu____14079 = (

let uu___207_14080 = x
in (

let uu____14081 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___207_14080.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___207_14080.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____14081}))
in ((uu____14079), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let uu____14087 = (FStar_List.fold_left (fun uu____14105 b -> (match (uu____14105) with
| (nbs', env1) -> begin
(

let b1 = (norm_binder cfg env1 b)
in (((b1)::nbs'), ((Dummy)::env1)))
end)) (([]), (env)) bs)
in (match (uu____14087) with
| (nbs, uu____14133) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags = (filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags)
in (

let uu____14149 = (

let uu___208_14150 = rc
in (

let uu____14151 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___208_14150.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____14151; FStar_Syntax_Syntax.residual_flags = uu___208_14150.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____14149)))
end
| uu____14158 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 t -> (match (stack1) with
| [] -> begin
t
end
| (Debug (tm))::stack2 -> begin
((

let uu____14170 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms")))
in (match (uu____14170) with
| true -> begin
(

let uu____14171 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____14172 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Normalized %s to %s\n" uu____14171 uu____14172)))
end
| uu____14173 -> begin
()
end));
(rebuild cfg env stack2 t);
)
end
| (Steps (s, ps, dl))::stack2 -> begin
(rebuild (

let uu___209_14190 = cfg
in {steps = s; tcenv = uu___209_14190.tcenv; delta_level = dl; primitive_steps = ps}) env stack2 t)
end
| (Meta (m, r))::stack2 -> begin
(

let t1 = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack2 t1))
end
| (MemoLazy (r))::stack2 -> begin
((set_memo r ((env), (t)));
(log cfg (fun uu____14219 -> (

let uu____14220 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" uu____14220))));
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

let uu____14256 = (

let uu___210_14257 = (FStar_Syntax_Util.abs bs1 t lopt1)
in {FStar_Syntax_Syntax.n = uu___210_14257.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___210_14257.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack2 uu____14256))))
end
| (Arg (Univ (uu____14258), uu____14259, uu____14260))::uu____14261 -> begin
(failwith "Impossible")
end
| (Arg (Dummy, uu____14264, uu____14265))::uu____14266 -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack2 -> begin
(

let t1 = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack2 t1))
end
| (Arg (Clos (env1, tm, m, uu____14282), aq, r))::stack2 -> begin
((log cfg (fun uu____14311 -> (

let uu____14312 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" uu____14312))));
(match ((FStar_List.contains (Exclude (Iota)) cfg.steps)) with
| true -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let arg = (closure_as_term cfg env1 tm)
in (

let t1 = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack2 t1)))
end
| uu____14317 -> begin
(

let stack3 = (App (((t), (aq), (r))))::stack2
in (norm cfg env1 stack3 tm))
end)
end
| uu____14321 -> begin
(

let uu____14322 = (FStar_ST.read m)
in (match (uu____14322) with
| FStar_Pervasives_Native.None -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let arg = (closure_as_term cfg env1 tm)
in (

let t1 = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack2 t1)))
end
| uu____14351 -> begin
(

let stack3 = (MemoLazy (m))::(App (((t), (aq), (r))))::stack2
in (norm cfg env1 stack3 tm))
end)
end
| FStar_Pervasives_Native.Some (uu____14358, a) -> begin
(

let t1 = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack2 t1))
end))
end);
)
end
| (App (head1, aq, r))::stack2 -> begin
(

let t1 = (FStar_Syntax_Syntax.extend_app head1 ((t), (aq)) FStar_Pervasives_Native.None r)
in (

let uu____14382 = (maybe_simplify cfg t1)
in (rebuild cfg env stack2 uu____14382)))
end
| (Match (env1, branches, r))::stack2 -> begin
((log cfg (fun uu____14392 -> (

let uu____14393 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" uu____14393))));
(

let scrutinee = t
in (

let norm_and_rebuild_match = (fun uu____14398 -> ((log cfg (fun uu____14403 -> (

let uu____14404 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____14405 = (

let uu____14406 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____14423 -> (match (uu____14423) with
| (p, uu____14433, uu____14434) -> begin
(FStar_Syntax_Print.pat_to_string p)
end))))
in (FStar_All.pipe_right uu____14406 (FStar_String.concat "\n\t")))
in (FStar_Util.print2 "match is irreducible: scrutinee=%s\nbranches=%s\n" uu____14404 uu____14405)))));
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg_exclude_iota_zeta = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun uu___152_14451 -> (match (uu___152_14451) with
| FStar_TypeChecker_Env.Inlining -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| uu____14452 -> begin
false
end))))
in (

let steps' = (

let uu____14456 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____14456) with
| true -> begin
(Exclude (Zeta))::[]
end
| uu____14459 -> begin
(Exclude (Iota))::(Exclude (Zeta))::[]
end))
in (

let uu___211_14460 = cfg
in {steps = (FStar_List.append steps' cfg.steps); tcenv = uu___211_14460.tcenv; delta_level = new_delta; primitive_steps = uu___211_14460.primitive_steps})))
in (

let norm_or_whnf = (fun env2 t1 -> (match (whnf) with
| true -> begin
(closure_as_term cfg_exclude_iota_zeta env2 t1)
end
| uu____14472 -> begin
(norm cfg_exclude_iota_zeta env2 [] t1)
end))
in (

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____14504) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____14527 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____14593 uu____14594 -> (match (((uu____14593), (uu____14594))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____14697 = (norm_pat env3 p1)
in (match (uu____14697) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____14527) with
| (pats1, env3) -> begin
(((

let uu___212_14799 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___212_14799.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___213_14818 = x
in (

let uu____14819 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___213_14818.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___213_14818.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____14819}))
in (((

let uu___214_14827 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___214_14827.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___215_14832 = x
in (

let uu____14833 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___215_14832.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___215_14832.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____14833}))
in (((

let uu___216_14841 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___216_14841.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t1) -> begin
(

let x1 = (

let uu___217_14851 = x
in (

let uu____14852 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___217_14851.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___217_14851.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____14852}))
in (

let t2 = (norm_or_whnf env2 t1)
in (((

let uu___218_14861 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t2))); FStar_Syntax_Syntax.p = uu___218_14861.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let branches1 = (match (env1) with
| [] when whnf -> begin
branches
end
| uu____14865 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch1 -> (

let uu____14879 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____14879) with
| (p, wopt, e) -> begin
(

let uu____14899 = (norm_pat env1 p)
in (match (uu____14899) with
| (p1, env2) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____14930 = (norm_or_whnf env2 w)
in FStar_Pervasives_Native.Some (uu____14930))
end)
in (

let e1 = (norm_or_whnf env2 e)
in (FStar_Syntax_Util.branch ((p1), (wopt1), (e1)))))
end))
end)))))
end)
in (

let uu____14936 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches1)))) r)
in (rebuild cfg env1 stack2 uu____14936)))))));
))
in (

let rec is_cons = (fun head1 -> (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, uu____14946) -> begin
(is_cons h)
end
| FStar_Syntax_Syntax.Tm_constant (uu____14951) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____14952; FStar_Syntax_Syntax.fv_delta = uu____14953; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____14954; FStar_Syntax_Syntax.fv_delta = uu____14955; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____14956))}) -> begin
true
end
| uu____14963 -> begin
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

let uu____15092 = (FStar_Syntax_Util.head_and_args scrutinee1)
in (match (uu____15092) with
| (head1, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____15141) -> begin
FStar_Util.Inl ((scrutinee_orig)::[])
end
| FStar_Syntax_Syntax.Pat_wild (uu____15144) -> begin
FStar_Util.Inl ((scrutinee_orig)::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____15147) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| uu____15166 -> begin
(

let uu____15167 = (

let uu____15168 = (is_cons head1)
in (not (uu____15168)))
in FStar_Util.Inr (uu____15167))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let uu____15189 = (

let uu____15190 = (FStar_Syntax_Util.un_uinst head1)
in uu____15190.FStar_Syntax_Syntax.n)
in (match (uu____15189) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| uu____15200 -> begin
(

let uu____15201 = (

let uu____15202 = (is_cons head1)
in (not (uu____15202)))
in FStar_Util.Inr (uu____15201))
end))
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t1, uu____15255))::rest_a, ((p1, uu____15258))::rest_p) -> begin
(

let uu____15302 = (matches_pat t1 p1)
in (match (uu____15302) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____15327 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee1 p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p1, wopt, b))::rest -> begin
(

let uu____15429 = (matches_pat scrutinee1 p1)
in (match (uu____15429) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee1 rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
((log cfg (fun uu____15449 -> (

let uu____15450 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____15451 = (

let uu____15452 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right uu____15452 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" uu____15450 uu____15451)))));
(

let env2 = (FStar_List.fold_left (fun env2 t1 -> (

let uu____15469 = (

let uu____15470 = (

let uu____15489 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ((([]), (t1)))))
in (([]), (t1), (uu____15489), (false)))
in Clos (uu____15470))
in (uu____15469)::env2)) env1 s)
in (

let uu____15530 = (guard_when_clause wopt b rest)
in (norm cfg env2 stack2 uu____15530)));
)
end))
end))
in (

let uu____15531 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota))))
in (match (uu____15531) with
| true -> begin
(norm_and_rebuild_match ())
end
| uu____15532 -> begin
(matches scrutinee branches)
end))))))));
)
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun uu___153_15554 -> (match (uu___153_15554) with
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
| uu____15558 -> begin
[]
end))))
in (

let d1 = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| uu____15564 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d1; primitive_steps = built_in_primitive_steps})))


let normalize_with_primitive_steps : primitive_step Prims.list  ->  step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun ps s e t -> (

let c = (config s e)
in (

let c1 = (

let uu___219_15593 = (config s e)
in {steps = uu___219_15593.steps; tcenv = uu___219_15593.tcenv; delta_level = uu___219_15593.delta_level; primitive_steps = (FStar_List.append c.primitive_steps ps)})
in (norm c1 [] [] t))))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (normalize_with_primitive_steps [] s e t))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (

let uu____15618 = (config s e)
in (norm_comp uu____15618 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let uu____15627 = (config [] env)
in (norm_universe uu____15627 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (

let uu____15636 = (config [] env)
in (ghost_to_pure_aux uu____15636 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (

let uu____15650 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____15650)))
in (

let uu____15651 = ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ))
in (match (uu____15651) with
| true -> begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let uu___220_15653 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = uu___220_15653.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___220_15653.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____15656 -> (

let uu____15657 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env uu____15657)))})
end
| FStar_Pervasives_Native.None -> begin
lc
end)
end
| uu____15658 -> begin
lc
end)))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (

let t1 = try
(match (()) with
| () -> begin
(normalize ((AllowUnboundUniverses)::[]) env t)
end)
with
| e -> begin
((

let uu____15676 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_warning "Normalization failed with error %s" uu____15676));
t;
)
end
in (FStar_Syntax_Print.term_to_string t1)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let c1 = try
(match (()) with
| () -> begin
(

let uu____15689 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp uu____15689 [] c))
end)
with
| e -> begin
((

let uu____15696 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_warning "Normalization failed with error %s" uu____15696));
c;
)
end
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

let uu____15736 = (

let uu____15737 = (

let uu____15744 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (uu____15744)))
in FStar_Syntax_Syntax.Tm_refine (uu____15737))
in (mk uu____15736 t01.FStar_Syntax_Syntax.pos))
end
| uu____15749 -> begin
t2
end))
end
| uu____15750 -> begin
t2
end)))
in (aux t))))


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((WHNF)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Beta)::[]) env t))


let reduce_or_remove_uvar_solutions : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun remove env t -> (normalize (FStar_List.append (match (remove) with
| true -> begin
(CheckNoUvars)::[]
end
| uu____15773 -> begin
[]
end) ((Beta)::(NoDeltaSteps)::(CompressUvars)::(Exclude (Zeta))::(Exclude (Iota))::(NoFullNorm)::[])) env t))


let reduce_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions false env t))


let remove_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions true env t))


let eta_expand_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e t_e -> (

let uu____15802 = (FStar_Syntax_Util.arrow_formals_comp t_e)
in (match (uu____15802) with
| (formals, c) -> begin
(match (formals) with
| [] -> begin
e
end
| uu____15831 -> begin
(

let uu____15838 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____15838) with
| (actuals, uu____15848, uu____15849) -> begin
(match (((FStar_List.length actuals) = (FStar_List.length formals))) with
| true -> begin
e
end
| uu____15862 -> begin
(

let uu____15863 = (FStar_All.pipe_right formals FStar_Syntax_Util.args_of_binders)
in (match (uu____15863) with
| (binders, args) -> begin
(

let uu____15880 = (FStar_Syntax_Syntax.mk_Tm_app e args FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Util.abs binders uu____15880 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c)))))
end))
end)
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(eta_expand_with_type env t x.FStar_Syntax_Syntax.sort)
end
| uu____15890 -> begin
(

let uu____15891 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____15891) with
| (head1, args) -> begin
(

let uu____15928 = (

let uu____15929 = (FStar_Syntax_Subst.compress head1)
in uu____15929.FStar_Syntax_Syntax.n)
in (match (uu____15928) with
| FStar_Syntax_Syntax.Tm_uvar (uu____15932, thead) -> begin
(

let uu____15958 = (FStar_Syntax_Util.arrow_formals thead)
in (match (uu____15958) with
| (formals, tres) -> begin
(match (((FStar_List.length formals) = (FStar_List.length args))) with
| true -> begin
t
end
| uu____15999 -> begin
(

let uu____16000 = (env.FStar_TypeChecker_Env.type_of (

let uu___225_16008 = env
in {FStar_TypeChecker_Env.solver = uu___225_16008.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___225_16008.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___225_16008.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___225_16008.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___225_16008.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___225_16008.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___225_16008.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___225_16008.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___225_16008.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___225_16008.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___225_16008.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___225_16008.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___225_16008.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___225_16008.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___225_16008.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___225_16008.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___225_16008.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___225_16008.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___225_16008.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___225_16008.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___225_16008.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___225_16008.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___225_16008.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___225_16008.FStar_TypeChecker_Env.is_native_tactic}) t)
in (match (uu____16000) with
| (uu____16009, ty, uu____16011) -> begin
(eta_expand_with_type env t ty)
end))
end)
end))
end
| uu____16012 -> begin
(

let uu____16013 = (env.FStar_TypeChecker_Env.type_of (

let uu___226_16021 = env
in {FStar_TypeChecker_Env.solver = uu___226_16021.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___226_16021.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___226_16021.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___226_16021.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___226_16021.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___226_16021.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___226_16021.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___226_16021.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___226_16021.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___226_16021.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___226_16021.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___226_16021.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___226_16021.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___226_16021.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___226_16021.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___226_16021.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___226_16021.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___226_16021.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___226_16021.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___226_16021.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___226_16021.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___226_16021.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___226_16021.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___226_16021.FStar_TypeChecker_Env.is_native_tactic}) t)
in (match (uu____16013) with
| (uu____16022, ty, uu____16024) -> begin
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
| (uu____16102, FStar_Util.Inr (c)) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
end
| (uu____16108, FStar_Util.Inl (t)) -> begin
(

let uu____16114 = (

let uu____16117 = (

let uu____16118 = (

let uu____16131 = (FStar_Syntax_Syntax.mk_Total t)
in ((binders), (uu____16131)))
in FStar_Syntax_Syntax.Tm_arrow (uu____16118))
in (FStar_Syntax_Syntax.mk uu____16117))
in (uu____16114 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end)
in (

let uu____16135 = (FStar_Syntax_Subst.open_univ_vars univ_names t)
in (match (uu____16135) with
| (univ_names1, t1) -> begin
(

let t2 = (remove_uvar_solutions env t1)
in (

let t3 = (FStar_Syntax_Subst.close_univ_vars univ_names1 t2)
in (

let uu____16162 = (match (binders) with
| [] -> begin
(([]), (FStar_Util.Inl (t3)))
end
| uu____16217 -> begin
(

let uu____16218 = (

let uu____16227 = (

let uu____16228 = (FStar_Syntax_Subst.compress t3)
in uu____16228.FStar_Syntax_Syntax.n)
in ((uu____16227), (tc)))
in (match (uu____16218) with
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inr (uu____16253)) -> begin
((binders1), (FStar_Util.Inr (c)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inl (uu____16290)) -> begin
((binders1), (FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))))
end
| (uu____16329, FStar_Util.Inl (uu____16330)) -> begin
(([]), (FStar_Util.Inl (t3)))
end
| uu____16353 -> begin
(failwith "Impossible")
end))
end)
in (match (uu____16162) with
| (binders1, tc1) -> begin
((univ_names1), (binders1), (tc1))
end))))
end))))


let elim_uvars_aux_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term) = (fun env univ_names binders t -> (

let uu____16462 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl (t)))
in (match (uu____16462) with
| (univ_names1, binders1, tc) -> begin
(

let uu____16520 = (FStar_Util.left tc)
in ((univ_names1), (binders1), (uu____16520)))
end)))


let elim_uvars_aux_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) = (fun env univ_names binders c -> (

let uu____16559 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr (c)))
in (match (uu____16559) with
| (univ_names1, binders1, tc) -> begin
(

let uu____16619 = (FStar_Util.right tc)
in ((univ_names1), (binders1), (uu____16619)))
end)))


let rec elim_uvars : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, lids, lids') -> begin
(

let uu____16654 = (elim_uvars_aux_t env univ_names binders typ)
in (match (uu____16654) with
| (univ_names1, binders1, typ1) -> begin
(

let uu___227_16682 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univ_names1), (binders1), (typ1), (lids), (lids'))); FStar_Syntax_Syntax.sigrng = uu___227_16682.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___227_16682.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___227_16682.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___227_16682.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uu___228_16703 = s
in (

let uu____16704 = (

let uu____16705 = (

let uu____16714 = (FStar_List.map (elim_uvars env) sigs)
in ((uu____16714), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____16705))
in {FStar_Syntax_Syntax.sigel = uu____16704; FStar_Syntax_Syntax.sigrng = uu___228_16703.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___228_16703.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___228_16703.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___228_16703.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univ_names, typ, lident, i, lids) -> begin
(

let uu____16731 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____16731) with
| (univ_names1, uu____16749, typ1) -> begin
(

let uu___229_16763 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univ_names1), (typ1), (lident), (i), (lids))); FStar_Syntax_Syntax.sigrng = uu___229_16763.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___229_16763.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___229_16763.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___229_16763.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) -> begin
(

let uu____16769 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____16769) with
| (univ_names1, uu____16787, typ1) -> begin
(

let uu___230_16801 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (univ_names1), (typ1))); FStar_Syntax_Syntax.sigrng = uu___230_16801.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___230_16801.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___230_16801.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___230_16801.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____16835 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____16835) with
| (opening, lbunivs) -> begin
(

let elim = (fun t -> (

let uu____16858 = (

let uu____16859 = (FStar_Syntax_Subst.subst opening t)
in (remove_uvar_solutions env uu____16859))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____16858)))
in (

let lbtyp = (elim lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (elim lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___231_16862 = lb
in {FStar_Syntax_Syntax.lbname = uu___231_16862.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___231_16862.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}))))
end)))))
in (

let uu___232_16863 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((b), (lbs1))), (lids))); FStar_Syntax_Syntax.sigrng = uu___232_16863.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___232_16863.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___232_16863.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___232_16863.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(

let uu___233_16875 = s
in (

let uu____16876 = (

let uu____16877 = (remove_uvar_solutions env t)
in FStar_Syntax_Syntax.Sig_main (uu____16877))
in {FStar_Syntax_Syntax.sigel = uu____16876; FStar_Syntax_Syntax.sigrng = uu___233_16875.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___233_16875.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___233_16875.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___233_16875.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, t) -> begin
(

let uu____16881 = (elim_uvars_aux_t env us [] t)
in (match (uu____16881) with
| (us1, uu____16899, t1) -> begin
(

let uu___234_16913 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((l), (us1), (t1))); FStar_Syntax_Syntax.sigrng = uu___234_16913.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___234_16913.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___234_16913.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___234_16913.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____16914) -> begin
(failwith "Impossible: should have been desugared already")
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____16916 = (elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____16916) with
| (univs1, binders, signature) -> begin
(

let uu____16944 = (

let uu____16953 = (FStar_Syntax_Subst.univ_var_opening univs1)
in (match (uu____16953) with
| (univs_opening, univs2) -> begin
(

let uu____16980 = (FStar_Syntax_Subst.univ_var_closing univs2)
in ((univs_opening), (uu____16980)))
end))
in (match (uu____16944) with
| (univs_opening, univs_closing) -> begin
(

let uu____16997 = (

let binders1 = (FStar_Syntax_Subst.open_binders binders)
in (

let uu____17003 = (FStar_Syntax_Subst.opening_of_binders binders1)
in (

let uu____17004 = (FStar_Syntax_Subst.closing_of_binders binders1)
in ((uu____17003), (uu____17004)))))
in (match (uu____16997) with
| (b_opening, b_closing) -> begin
(

let n1 = (FStar_List.length univs1)
in (

let n_binders = (FStar_List.length binders)
in (

let elim_tscheme = (fun uu____17026 -> (match (uu____17026) with
| (us, t) -> begin
(

let n_us = (FStar_List.length us)
in (

let uu____17044 = (FStar_Syntax_Subst.open_univ_vars us t)
in (match (uu____17044) with
| (us1, t1) -> begin
(

let uu____17055 = (

let uu____17060 = (FStar_All.pipe_right b_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____17067 = (FStar_All.pipe_right b_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____17060), (uu____17067))))
in (match (uu____17055) with
| (b_opening1, b_closing1) -> begin
(

let uu____17080 = (

let uu____17085 = (FStar_All.pipe_right univs_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____17094 = (FStar_All.pipe_right univs_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____17085), (uu____17094))))
in (match (uu____17080) with
| (univs_opening1, univs_closing1) -> begin
(

let t2 = (

let uu____17110 = (FStar_Syntax_Subst.subst b_opening1 t1)
in (FStar_Syntax_Subst.subst univs_opening1 uu____17110))
in (

let uu____17111 = (elim_uvars_aux_t env [] [] t2)
in (match (uu____17111) with
| (uu____17132, uu____17133, t3) -> begin
(

let t4 = (

let uu____17148 = (

let uu____17149 = (FStar_Syntax_Subst.close_univ_vars us1 t3)
in (FStar_Syntax_Subst.subst b_closing1 uu____17149))
in (FStar_Syntax_Subst.subst univs_closing1 uu____17148))
in ((us1), (t4)))
end)))
end))
end))
end)))
end))
in (

let elim_term = (fun t -> (

let uu____17154 = (elim_uvars_aux_t env univs1 binders t)
in (match (uu____17154) with
| (uu____17167, uu____17168, t1) -> begin
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
| uu____17228 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((a.FStar_Syntax_Syntax.action_params), (body), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
end))
in (

let destruct_action_body = (fun body -> (

let uu____17245 = (

let uu____17246 = (FStar_Syntax_Subst.compress body)
in uu____17246.FStar_Syntax_Syntax.n)
in (match (uu____17245) with
| FStar_Syntax_Syntax.Tm_ascribed (defn, (FStar_Util.Inl (typ), FStar_Pervasives_Native.None), FStar_Pervasives_Native.None) -> begin
((defn), (typ))
end
| uu____17305 -> begin
(failwith "Impossible")
end)))
in (

let destruct_action_typ_templ = (fun t -> (

let uu____17334 = (

let uu____17335 = (FStar_Syntax_Subst.compress t)
in uu____17335.FStar_Syntax_Syntax.n)
in (match (uu____17334) with
| FStar_Syntax_Syntax.Tm_abs (pars, body, uu____17356) -> begin
(

let uu____17377 = (destruct_action_body body)
in (match (uu____17377) with
| (defn, typ) -> begin
((pars), (defn), (typ))
end))
end
| uu____17422 -> begin
(

let uu____17423 = (destruct_action_body t)
in (match (uu____17423) with
| (defn, typ) -> begin
(([]), (defn), (typ))
end))
end)))
in (

let uu____17472 = (elim_tscheme ((a.FStar_Syntax_Syntax.action_univs), (action_typ_templ)))
in (match (uu____17472) with
| (action_univs, t) -> begin
(

let uu____17481 = (destruct_action_typ_templ t)
in (match (uu____17481) with
| (action_params, action_defn, action_typ) -> begin
(

let a' = (

let uu___235_17522 = a
in {FStar_Syntax_Syntax.action_name = uu___235_17522.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___235_17522.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action_univs; FStar_Syntax_Syntax.action_params = action_params; FStar_Syntax_Syntax.action_defn = action_defn; FStar_Syntax_Syntax.action_typ = action_typ})
in a')
end))
end))))))
in (

let ed1 = (

let uu___236_17524 = ed
in (

let uu____17525 = (elim_tscheme ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____17526 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____17527 = (elim_tscheme ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____17528 = (elim_tscheme ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____17529 = (elim_tscheme ed.FStar_Syntax_Syntax.stronger)
in (

let uu____17530 = (elim_tscheme ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____17531 = (elim_tscheme ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____17532 = (elim_tscheme ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____17533 = (elim_tscheme ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____17534 = (elim_tscheme ed.FStar_Syntax_Syntax.trivial)
in (

let uu____17535 = (elim_term ed.FStar_Syntax_Syntax.repr)
in (

let uu____17536 = (elim_tscheme ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____17537 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____17538 = (FStar_List.map elim_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___236_17524.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___236_17524.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu____17525; FStar_Syntax_Syntax.bind_wp = uu____17526; FStar_Syntax_Syntax.if_then_else = uu____17527; FStar_Syntax_Syntax.ite_wp = uu____17528; FStar_Syntax_Syntax.stronger = uu____17529; FStar_Syntax_Syntax.close_wp = uu____17530; FStar_Syntax_Syntax.assert_p = uu____17531; FStar_Syntax_Syntax.assume_p = uu____17532; FStar_Syntax_Syntax.null_wp = uu____17533; FStar_Syntax_Syntax.trivial = uu____17534; FStar_Syntax_Syntax.repr = uu____17535; FStar_Syntax_Syntax.return_repr = uu____17536; FStar_Syntax_Syntax.bind_repr = uu____17537; FStar_Syntax_Syntax.actions = uu____17538})))))))))))))))
in (

let uu___237_17541 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ed1); FStar_Syntax_Syntax.sigrng = uu___237_17541.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___237_17541.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___237_17541.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___237_17541.FStar_Syntax_Syntax.sigattrs})))))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub_eff) -> begin
(

let elim_tscheme_opt = (fun uu___154_17558 -> (match (uu___154_17558) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (us, t) -> begin
(

let uu____17585 = (elim_uvars_aux_t env us [] t)
in (match (uu____17585) with
| (us1, uu____17609, t1) -> begin
FStar_Pervasives_Native.Some (((us1), (t1)))
end))
end))
in (

let sub_eff1 = (

let uu___238_17628 = sub_eff
in (

let uu____17629 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp)
in (

let uu____17632 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift)
in {FStar_Syntax_Syntax.source = uu___238_17628.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___238_17628.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = uu____17629; FStar_Syntax_Syntax.lift = uu____17632})))
in (

let uu___239_17635 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub_eff1); FStar_Syntax_Syntax.sigrng = uu___239_17635.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___239_17635.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___239_17635.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___239_17635.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univ_names, binders, comp, flags) -> begin
(

let uu____17645 = (elim_uvars_aux_c env univ_names binders comp)
in (match (uu____17645) with
| (univ_names1, binders1, comp1) -> begin
(

let uu___240_17679 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (univ_names1), (binders1), (comp1), (flags))); FStar_Syntax_Syntax.sigrng = uu___240_17679.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___240_17679.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___240_17679.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___240_17679.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_pragma (uu____17690) -> begin
s
end))




