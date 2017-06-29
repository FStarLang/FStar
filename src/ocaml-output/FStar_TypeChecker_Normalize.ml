
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
| uu____13 -> begin
false
end))


let uu___is_Iota : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iota -> begin
true
end
| uu____18 -> begin
false
end))


let uu___is_Zeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Zeta -> begin
true
end
| uu____23 -> begin
false
end))


let uu___is_Exclude : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
true
end
| uu____29 -> begin
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
| uu____42 -> begin
false
end))


let uu___is_Primops : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____47 -> begin
false
end))


let uu___is_Eager_unfolding : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding -> begin
true
end
| uu____52 -> begin
false
end))


let uu___is_Inlining : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____57 -> begin
false
end))


let uu___is_NoDeltaSteps : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoDeltaSteps -> begin
true
end
| uu____62 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____68 -> begin
false
end))


let __proj__UnfoldUntil__item___0 : step  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
_0
end))


let uu___is_UnfoldTac : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldTac -> begin
true
end
| uu____81 -> begin
false
end))


let uu___is_PureSubtermsWithinComputations : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PureSubtermsWithinComputations -> begin
true
end
| uu____86 -> begin
false
end))


let uu___is_Simplify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simplify -> begin
true
end
| uu____91 -> begin
false
end))


let uu___is_EraseUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EraseUniverses -> begin
true
end
| uu____96 -> begin
false
end))


let uu___is_AllowUnboundUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AllowUnboundUniverses -> begin
true
end
| uu____101 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____106 -> begin
false
end))


let uu___is_CompressUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CompressUvars -> begin
true
end
| uu____111 -> begin
false
end))


let uu___is_NoFullNorm : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoFullNorm -> begin
true
end
| uu____116 -> begin
false
end))


let uu___is_CheckNoUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckNoUvars -> begin
true
end
| uu____121 -> begin
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
| uu____243 -> begin
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
| uu____284 -> begin
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
| uu____297 -> begin
false
end))


type env =
closure Prims.list


let closure_to_string : closure  ->  Prims.string = (fun uu___138_302 -> (match (uu___138_302) with
| Clos (uu____303, t, uu____305, uu____306) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| Univ (uu____317) -> begin
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
| uu____467 -> begin
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
| uu____493 -> begin
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
| uu____519 -> begin
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
| uu____548 -> begin
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
| uu____577 -> begin
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
| uu____612 -> begin
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
| uu____637 -> begin
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
| uu____661 -> begin
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
| uu____692 -> begin
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
| uu____721 -> begin
false
end))


let __proj__Debug__item___0 : stack_elt  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
_0
end))


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r))


let set_memo = (fun r t -> (

let uu____777 = (FStar_ST.read r)
in (match (uu____777) with
| FStar_Pervasives_Native.Some (uu____782) -> begin
(failwith "Unexpected set_memo: thunk already evaluated")
end
| FStar_Pervasives_Native.None -> begin
(FStar_ST.write r (FStar_Pervasives_Native.Some (t)))
end)))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (

let uu____792 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right uu____792 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun uu___139_798 -> (match (uu___139_798) with
| Arg (c, uu____800, uu____801) -> begin
(

let uu____802 = (closure_to_string c)
in (FStar_Util.format1 "Closure %s" uu____802))
end
| MemoLazy (uu____803) -> begin
"MemoLazy"
end
| Abs (uu____807, bs, uu____809, uu____810, uu____811) -> begin
(

let uu____814 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" uu____814))
end
| UnivArgs (uu____821) -> begin
"UnivArgs"
end
| Match (uu____825) -> begin
"Match"
end
| App (t, uu____830, uu____831) -> begin
(

let uu____832 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "App %s" uu____832))
end
| Meta (m, uu____834) -> begin
"Meta"
end
| Let (uu____835) -> begin
"Let"
end
| Steps (uu____840, uu____841, uu____842) -> begin
"Steps"
end
| Debug (t) -> begin
(

let uu____848 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Debug %s" uu____848))
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (

let uu____855 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right uu____855 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> (

let uu____871 = (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm")))
in (match (uu____871) with
| true -> begin
(f ())
end
| uu____872 -> begin
()
end)))


let is_empty = (fun uu___140_882 -> (match (uu___140_882) with
| [] -> begin
true
end
| uu____884 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| uu____909 -> begin
(

let uu____910 = (

let uu____911 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" uu____911))
in (failwith uu____910))
end)


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun l -> (match ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Pure_lid)
end
| uu____918 -> begin
(match ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Tot_lid)
end
| uu____920 -> begin
(match ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_PURE_lid)
end
| uu____922 -> begin
FStar_Pervasives_Native.None
end)
end)
end))


let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us1 = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let uu____946 = (FStar_List.fold_left (fun uu____964 u1 -> (match (uu____964) with
| (cur_kernel, cur_max, out) -> begin
(

let uu____979 = (FStar_Syntax_Util.univ_kernel u1)
in (match (uu____979) with
| (k_u, n1) -> begin
(

let uu____988 = (FStar_Syntax_Util.eq_univs cur_kernel k_u)
in (match (uu____988) with
| true -> begin
((cur_kernel), (u1), (out))
end
| uu____994 -> begin
((k_u), (u1), ((cur_max)::out))
end))
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us1)
in (match (uu____946) with
| (uu____998, u1, out) -> begin
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

let uu____1017 = (FStar_List.nth env x)
in (match (uu____1017) with
| Univ (u3) -> begin
(aux u3)
end
| Dummy -> begin
(u2)::[]
end
| uu____1020 -> begin
(failwith "Impossible: universe variable bound to a term")
end))
end)
with
| uu____1027 -> begin
(

let uu____1028 = (FStar_All.pipe_right cfg.steps (FStar_List.contains AllowUnboundUniverses))
in (match (uu____1028) with
| true -> begin
(FStar_Syntax_Syntax.U_unknown)::[]
end
| uu____1030 -> begin
(failwith "Universe variable not found")
end))
end
end
| FStar_Syntax_Syntax.U_unif (uu____1032) when (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars)) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_zero -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_unif (uu____1037) -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_name (uu____1042) -> begin
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

let uu____1047 = (FStar_List.collect aux us)
in (FStar_All.pipe_right uu____1047 norm_univs))
in (match (us1) with
| (u_k)::(hd1)::rest -> begin
(

let rest1 = (hd1)::rest
in (

let uu____1058 = (FStar_Syntax_Util.univ_kernel u_k)
in (match (uu____1058) with
| (FStar_Syntax_Syntax.U_zero, n1) -> begin
(

let uu____1063 = (FStar_All.pipe_right rest1 (FStar_List.for_all (fun u3 -> (

let uu____1070 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____1070) with
| (uu____1073, m) -> begin
(n1 <= m)
end)))))
in (match (uu____1063) with
| true -> begin
rest1
end
| uu____1076 -> begin
us1
end))
end
| uu____1077 -> begin
us1
end)))
end
| uu____1080 -> begin
us1
end))
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1083 = (aux u3)
in (FStar_List.map (fun _0_40 -> FStar_Syntax_Syntax.U_succ (_0_40)) uu____1083))
end)))
in (

let uu____1085 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____1085) with
| true -> begin
FStar_Syntax_Syntax.U_unknown
end
| uu____1086 -> begin
(

let uu____1087 = (aux u)
in (match (uu____1087) with
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


let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> ((log cfg (fun uu____1178 -> (

let uu____1179 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1180 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1179 uu____1180)))));
(match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| uu____1181 -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1184) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.tk FStar_Pervasives_Native.None);
t1;
)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1203) -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.tk FStar_Pervasives_Native.None);
t1;
)
end
| FStar_Syntax_Syntax.Tm_name (uu____1208) -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.tk FStar_Pervasives_Native.None);
t1;
)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1213) -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.tk FStar_Pervasives_Native.None);
t1;
)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1218) -> begin
(

let uu____1229 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____1229) with
| true -> begin
(

let uu____1230 = (

let uu____1231 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____1232 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s): CheckNoUvars: Unexpected unification variable remains: %s" uu____1231 uu____1232)))
in (failwith uu____1230))
end
| uu____1233 -> begin
t1
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____1235 = (

let uu____1236 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (uu____1236))
in (mk uu____1235 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let uu____1243 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1243))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____1245 = (lookup_bvar env x)
in (match (uu____1245) with
| Univ (uu____1246) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t1
end
| Clos (env1, t0, r, uu____1250) -> begin
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

let uu____1308 = (closures_as_binders_delayed cfg env bs)
in (match (uu____1308) with
| (bs1, env1) -> begin
(

let body1 = (closure_as_term_delayed cfg env1 body)
in (

let uu____1328 = (

let uu____1329 = (

let uu____1339 = (close_lcomp_opt cfg env1 lopt)
in ((bs1), (body1), (uu____1339)))
in FStar_Syntax_Syntax.Tm_abs (uu____1329))
in (mk uu____1328 t1.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1359 = (closures_as_binders_delayed cfg env bs)
in (match (uu____1359) with
| (bs1, env1) -> begin
(

let c1 = (close_comp cfg env1 c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs1), (c1)))) t1.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____1390 = (

let uu____1397 = (

let uu____1401 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1401)::[])
in (closures_as_binders_delayed cfg env uu____1397))
in (match (uu____1390) with
| (x1, env1) -> begin
(

let phi1 = (closure_as_term_delayed cfg env1 phi)
in (

let uu____1415 = (

let uu____1416 = (

let uu____1421 = (

let uu____1422 = (FStar_List.hd x1)
in (FStar_All.pipe_right uu____1422 FStar_Pervasives_Native.fst))
in ((uu____1421), (phi1)))
in FStar_Syntax_Syntax.Tm_refine (uu____1416))
in (mk uu____1415 t1.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (annot, tacopt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____1490 = (closure_as_term_delayed cfg env t2)
in FStar_Util.Inl (uu____1490))
end
| FStar_Util.Inr (c) -> begin
(

let uu____1504 = (close_comp cfg env c)
in FStar_Util.Inr (uu____1504))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (closure_as_term_delayed cfg env))
in (

let uu____1519 = (

let uu____1520 = (

let uu____1538 = (closure_as_term_delayed cfg env t11)
in ((uu____1538), (((annot1), (tacopt1))), (lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____1520))
in (mk uu____1519 t1.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____1576 = (

let uu____1577 = (

let uu____1582 = (closure_as_term_delayed cfg env t')
in (

let uu____1585 = (

let uu____1586 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (uu____1586))
in ((uu____1582), (uu____1585))))
in FStar_Syntax_Syntax.Tm_meta (uu____1577))
in (mk uu____1576 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(

let uu____1628 = (

let uu____1629 = (

let uu____1634 = (closure_as_term_delayed cfg env t')
in (

let uu____1637 = (

let uu____1638 = (

let uu____1643 = (closure_as_term_delayed cfg env tbody)
in ((m), (uu____1643)))
in FStar_Syntax_Syntax.Meta_monadic (uu____1638))
in ((uu____1634), (uu____1637))))
in FStar_Syntax_Syntax.Tm_meta (uu____1629))
in (mk uu____1628 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody)) -> begin
(

let uu____1662 = (

let uu____1663 = (

let uu____1668 = (closure_as_term_delayed cfg env t')
in (

let uu____1671 = (

let uu____1672 = (

let uu____1678 = (closure_as_term_delayed cfg env tbody)
in ((m1), (m2), (uu____1678)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____1672))
in ((uu____1668), (uu____1671))))
in FStar_Syntax_Syntax.Tm_meta (uu____1663))
in (mk uu____1662 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(

let uu____1691 = (

let uu____1692 = (

let uu____1697 = (closure_as_term_delayed cfg env t')
in ((uu____1697), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____1692))
in (mk uu____1691 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env1 = (FStar_List.fold_left (fun env1 uu____1720 -> (Dummy)::env1) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____1726 = (

let uu____1733 = (FStar_Syntax_Syntax.is_top_level ((lb)::[]))
in (match (uu____1733) with
| true -> begin
((lb.FStar_Syntax_Syntax.lbname), (body))
end
| uu____1744 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1746 = (closure_as_term cfg ((Dummy)::env0) body)
in ((FStar_Util.Inl ((

let uu___155_1750 = x
in {FStar_Syntax_Syntax.ppname = uu___155_1750.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___155_1750.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = typ}))), (uu____1746))))
end))
in (match (uu____1726) with
| (nm, body1) -> begin
(

let lb1 = (

let uu___156_1762 = lb
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___156_1762.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = uu___156_1762.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (body1)))) t1.FStar_Syntax_Syntax.pos))
end))))))
end
| FStar_Syntax_Syntax.Tm_let ((uu____1769, lbs), body) -> begin
(

let norm_one_lb = (fun env1 lb -> (

let env_univs = (FStar_List.fold_right (fun uu____1795 env2 -> (Dummy)::env2) lb.FStar_Syntax_Syntax.lbunivs env1)
in (

let env2 = (

let uu____1800 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____1800) with
| true -> begin
env_univs
end
| uu____1802 -> begin
(FStar_List.fold_right (fun uu____1806 env2 -> (Dummy)::env2) lbs env_univs)
end))
in (

let ty = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (

let nm = (

let uu____1813 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____1813) with
| true -> begin
lb.FStar_Syntax_Syntax.lbname
end
| uu____1816 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_All.pipe_right (

let uu___157_1821 = x
in {FStar_Syntax_Syntax.ppname = uu___157_1821.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___157_1821.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty}) (fun _0_41 -> FStar_Util.Inl (_0_41))))
end))
in (

let uu___158_1822 = lb
in (

let uu____1823 = (closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___158_1822.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___158_1822.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____1823})))))))
in (

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body1 = (

let body_env = (FStar_List.fold_right (fun uu____1836 env1 -> (Dummy)::env1) lbs1 env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs1))), (body1)))) t1.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let head2 = (closure_as_term cfg env head1)
in (

let norm_one_branch = (fun env1 uu____1887 -> (match (uu____1887) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____1925) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1938 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1976 uu____1977 -> (match (((uu____1976), (uu____1977))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____2031 = (norm_pat env3 p1)
in (match (uu____2031) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____1938) with
| (pats1, env3) -> begin
(((

let uu___159_2085 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___159_2085.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___160_2096 = x
in (

let uu____2097 = (closure_as_term cfg env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___160_2096.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_2096.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2097}))
in (((

let uu___161_2103 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___161_2103.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___162_2107 = x
in (

let uu____2108 = (closure_as_term cfg env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___162_2107.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___162_2107.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2108}))
in (((

let uu___163_2114 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___163_2114.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t2) -> begin
(

let x1 = (

let uu___164_2123 = x
in (

let uu____2124 = (closure_as_term cfg env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___164_2123.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___164_2123.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2124}))
in (

let t3 = (closure_as_term cfg env2 t2)
in (((

let uu___165_2131 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t3))); FStar_Syntax_Syntax.p = uu___165_2131.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let uu____2133 = (norm_pat env1 pat)
in (match (uu____2133) with
| (pat1, env2) -> begin
(

let w_opt1 = (match (w_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____2153 = (closure_as_term cfg env2 w)
in FStar_Pervasives_Native.Some (uu____2153))
end)
in (

let tm1 = (closure_as_term cfg env2 tm)
in ((pat1), (w_opt1), (tm1))))
end)))
end))
in (

let uu____2157 = (

let uu____2158 = (

let uu____2173 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head2), (uu____2173)))
in FStar_Syntax_Syntax.Tm_match (uu____2158))
in (mk uu____2157 t1.FStar_Syntax_Syntax.pos))))
end))
end);
))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| uu____2220 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| uu____2236 -> begin
(FStar_List.map (fun uu____2250 -> (match (uu____2250) with
| (x, imp) -> begin
(

let uu____2265 = (closure_as_term_delayed cfg env x)
in ((uu____2265), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * closure Prims.list) = (fun cfg env bs -> (

let uu____2277 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2309 uu____2310 -> (match (((uu____2309), (uu____2310))) with
| ((env1, out), (b, imp)) -> begin
(

let b1 = (

let uu___166_2354 = b
in (

let uu____2355 = (closure_as_term_delayed cfg env1 b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___166_2354.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___166_2354.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2355}))
in (

let env2 = (Dummy)::env1
in ((env2), ((((b1), (imp)))::out))))
end)) ((env), ([]))))
in (match (uu____2277) with
| (env1, bs1) -> begin
(((FStar_List.rev bs1)), (env1))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| uu____2402 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____2414 = (closure_as_term_delayed cfg env t)
in (

let uu____2415 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____2414 uu____2415)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____2425 = (closure_as_term_delayed cfg env t)
in (

let uu____2426 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____2425 uu____2426)))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let rt = (closure_as_term_delayed cfg env c1.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c1.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___141_2445 -> (match (uu___141_2445) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____2449 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (uu____2449))
end
| f -> begin
f
end))))
in (

let uu____2453 = (

let uu___167_2454 = c1
in (

let uu____2455 = (FStar_List.map (norm_universe cfg env) c1.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = uu____2455; FStar_Syntax_Syntax.effect_name = uu___167_2454.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp uu____2453)))))
end)
end))
and filter_out_lcomp_cflags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun flags -> (FStar_All.pipe_right flags (FStar_List.filter (fun uu___142_2462 -> (match (uu___142_2462) with
| FStar_Syntax_Syntax.DECREASES (uu____2463) -> begin
false
end
| uu____2466 -> begin
true
end)))))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.filter (fun uu___143_2480 -> (match (uu___143_2480) with
| FStar_Syntax_Syntax.DECREASES (uu____2481) -> begin
false
end
| uu____2484 -> begin
true
end))))
in (

let rc1 = (

let uu___168_2486 = rc
in (

let uu____2487 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (closure_as_term cfg env))
in {FStar_Syntax_Syntax.residual_effect = uu___168_2486.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____2487; FStar_Syntax_Syntax.residual_flags = flags}))
in FStar_Pervasives_Native.Some (rc1)))
end
| uu____2493 -> begin
lopt
end))


let built_in_primitive_steps : primitive_step Prims.list = (

let const_as_tm = (fun c p -> (mk (FStar_Syntax_Syntax.Tm_constant (c)) p))
in (

let int_as_const = (fun p i -> (

let uu____2512 = (

let uu____2513 = (

let uu____2519 = (FStar_Util.string_of_int i)
in ((uu____2519), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____2513))
in (const_as_tm uu____2512 p)))
in (

let bool_as_const = (fun p b -> (const_as_tm (FStar_Const.Const_bool (b)) p))
in (

let string_as_const = (fun p b -> (const_as_tm (FStar_Const.Const_string ((((FStar_Util.bytes_of_string b)), (p)))) p))
in (

let arg_as_int = (fun uu____2546 -> (match (uu____2546) with
| (a, uu____2551) -> begin
(

let uu____2553 = (

let uu____2554 = (FStar_Syntax_Subst.compress a)
in uu____2554.FStar_Syntax_Syntax.n)
in (match (uu____2553) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, FStar_Pervasives_Native.None)) -> begin
(

let uu____2564 = (FStar_Util.int_of_string i)
in FStar_Pervasives_Native.Some (uu____2564))
end
| uu____2565 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_bounded_int = (fun uu____2574 -> (match (uu____2574) with
| (a, uu____2581) -> begin
(

let uu____2585 = (

let uu____2586 = (FStar_Syntax_Subst.compress a)
in uu____2586.FStar_Syntax_Syntax.n)
in (match (uu____2585) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv1); FStar_Syntax_Syntax.tk = uu____2593; FStar_Syntax_Syntax.pos = uu____2594; FStar_Syntax_Syntax.vars = uu____2595}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, FStar_Pervasives_Native.None)); FStar_Syntax_Syntax.tk = uu____2597; FStar_Syntax_Syntax.pos = uu____2598; FStar_Syntax_Syntax.vars = uu____2599}, uu____2600))::[]) when (FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") -> begin
(

let uu____2627 = (

let uu____2630 = (FStar_Util.int_of_string i)
in ((fv1), (uu____2630)))
in FStar_Pervasives_Native.Some (uu____2627))
end
| uu____2633 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_bool = (fun uu____2642 -> (match (uu____2642) with
| (a, uu____2647) -> begin
(

let uu____2649 = (

let uu____2650 = (FStar_Syntax_Subst.compress a)
in uu____2650.FStar_Syntax_Syntax.n)
in (match (uu____2649) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (b)) -> begin
FStar_Pervasives_Native.Some (b)
end
| uu____2655 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_char = (fun uu____2662 -> (match (uu____2662) with
| (a, uu____2667) -> begin
(

let uu____2669 = (

let uu____2670 = (FStar_Syntax_Subst.compress a)
in uu____2670.FStar_Syntax_Syntax.n)
in (match (uu____2669) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c)) -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____2675 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_string = (fun uu____2682 -> (match (uu____2682) with
| (a, uu____2687) -> begin
(

let uu____2689 = (

let uu____2690 = (FStar_Syntax_Subst.compress a)
in uu____2690.FStar_Syntax_Syntax.n)
in (match (uu____2689) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (bytes, uu____2695)) -> begin
FStar_Pervasives_Native.Some ((FStar_Util.string_of_bytes bytes))
end
| uu____2698 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_list = (fun f uu____2719 -> (match (uu____2719) with
| (a, uu____2728) -> begin
(

let rec sequence = (fun l -> (match (l) with
| [] -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Pervasives_Native.None)::uu____2745 -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.Some (x))::xs -> begin
(

let uu____2755 = (sequence xs)
in (match (uu____2755) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (xs') -> begin
FStar_Pervasives_Native.Some ((x)::xs')
end))
end))
in (

let uu____2766 = (FStar_Syntax_Util.list_elements a)
in (match (uu____2766) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (elts) -> begin
(

let uu____2776 = (FStar_List.map (fun x -> (

let uu____2783 = (FStar_Syntax_Syntax.as_arg x)
in (f uu____2783))) elts)
in (sequence uu____2776))
end)))
end))
in (

let lift_unary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a))::[] -> begin
(

let uu____2813 = (f a)
in FStar_Pervasives_Native.Some (uu____2813))
end
| uu____2814 -> begin
FStar_Pervasives_Native.None
end))
in (

let lift_binary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a0))::(FStar_Pervasives_Native.Some (a1))::[] -> begin
(

let uu____2853 = (f a0 a1)
in FStar_Pervasives_Native.Some (uu____2853))
end
| uu____2854 -> begin
FStar_Pervasives_Native.None
end))
in (

let unary_op = (fun as_a f r args -> (

let uu____2898 = (FStar_List.map as_a args)
in (lift_unary (f r) uu____2898)))
in (

let binary_op = (fun as_a f r args -> (

let uu____2948 = (FStar_List.map as_a args)
in (lift_binary (f r) uu____2948)))
in (

let as_primitive_step = (fun uu____2965 -> (match (uu____2965) with
| (l, arity, f) -> begin
{name = l; arity = arity; strong_reduction_ok = true; interpretation = f}
end))
in (

let unary_int_op = (fun f -> (unary_op arg_as_int (fun r x -> (

let uu____3006 = (f x)
in (int_as_const r uu____3006)))))
in (

let binary_int_op = (fun f -> (binary_op arg_as_int (fun r x y -> (

let uu____3033 = (f x y)
in (int_as_const r uu____3033)))))
in (

let unary_bool_op = (fun f -> (unary_op arg_as_bool (fun r x -> (

let uu____3053 = (f x)
in (bool_as_const r uu____3053)))))
in (

let binary_bool_op = (fun f -> (binary_op arg_as_bool (fun r x y -> (

let uu____3080 = (f x y)
in (bool_as_const r uu____3080)))))
in (

let binary_string_op = (fun f -> (binary_op arg_as_string (fun r x y -> (

let uu____3107 = (f x y)
in (string_as_const r uu____3107)))))
in (

let list_of_string' = (fun rng s -> (

let name = (fun l -> (

let uu____3121 = (

let uu____3122 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____3122))
in (mk uu____3121 rng)))
in (

let char_t = (name FStar_Parser_Const.char_lid)
in (

let charterm = (fun c -> (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))) rng))
in (

let uu____3132 = (

let uu____3134 = (FStar_String.list_of_string s)
in (FStar_List.map charterm uu____3134))
in (FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3132))))))
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

let uu____3187 = (arg_as_string a1)
in (match (uu____3187) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____3191 = (arg_as_list arg_as_string a2)
in (match (uu____3191) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.concat s1 s2)
in (

let uu____3199 = (string_as_const rng r)
in FStar_Pervasives_Native.Some (uu____3199)))
end
| uu____3200 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____3203 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____3205 -> begin
FStar_Pervasives_Native.None
end))
in (

let string_of_int1 = (fun rng i -> (

let uu____3216 = (FStar_Util.string_of_int i)
in (string_as_const rng uu____3216)))
in (

let string_of_bool1 = (fun rng b -> (string_as_const rng (match (b) with
| true -> begin
"true"
end
| uu____3224 -> begin
"false"
end)))
in (

let string_of_int2 = (fun rng i -> (

let uu____3232 = (FStar_Util.string_of_int i)
in (string_as_const rng uu____3232)))
in (

let string_of_bool2 = (fun rng b -> (string_as_const rng (match (b) with
| true -> begin
"true"
end
| uu____3240 -> begin
"false"
end)))
in (

let decidable_eq = (fun neg rng args -> (

let tru = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) rng)
in (

let fal = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) rng)
in (match (args) with
| ((_typ, uu____3261))::((a1, uu____3263))::((a2, uu____3265))::[] -> begin
(

let uu____3294 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____3294) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
fal
end
| uu____3300 -> begin
tru
end))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
tru
end
| uu____3305 -> begin
fal
end))
end
| uu____3306 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____3307 -> begin
(failwith "Unexpected number of arguments")
end))))
in (

let basic_ops = (

let uu____3319 = (

let uu____3329 = (

let uu____3339 = (

let uu____3349 = (

let uu____3359 = (

let uu____3369 = (

let uu____3379 = (

let uu____3389 = (

let uu____3399 = (

let uu____3409 = (

let uu____3419 = (

let uu____3429 = (

let uu____3439 = (

let uu____3449 = (

let uu____3459 = (

let uu____3469 = (

let uu____3479 = (

let uu____3489 = (

let uu____3499 = (

let uu____3509 = (

let uu____3519 = (

let uu____3528 = (FStar_Parser_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((uu____3528), ((Prims.parse_int "1")), ((unary_op arg_as_string list_of_string'))))
in (

let uu____3534 = (

let uu____3544 = (

let uu____3553 = (FStar_Parser_Const.p2l (("FStar")::("String")::("string_of_list")::[]))
in ((uu____3553), ((Prims.parse_int "1")), ((unary_op (arg_as_list arg_as_char) string_of_list'))))
in (

let uu____3560 = (

let uu____3570 = (

let uu____3582 = (FStar_Parser_Const.p2l (("FStar")::("String")::("concat")::[]))
in ((uu____3582), ((Prims.parse_int "2")), (string_concat')))
in (uu____3570)::[])
in (uu____3544)::uu____3560))
in (uu____3519)::uu____3534))
in (((FStar_Parser_Const.op_notEq), ((Prims.parse_int "3")), ((decidable_eq true))))::uu____3509)
in (((FStar_Parser_Const.op_Eq), ((Prims.parse_int "3")), ((decidable_eq false))))::uu____3499)
in (((FStar_Parser_Const.string_compare), ((Prims.parse_int "2")), ((binary_op arg_as_string string_compare'))))::uu____3489)
in (((FStar_Parser_Const.string_of_bool_lid), ((Prims.parse_int "1")), ((unary_op arg_as_bool string_of_bool2))))::uu____3479)
in (((FStar_Parser_Const.string_of_int_lid), ((Prims.parse_int "1")), ((unary_op arg_as_int string_of_int2))))::uu____3469)
in (((FStar_Parser_Const.strcat_lid'), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____3459)
in (((FStar_Parser_Const.strcat_lid), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____3449)
in (((FStar_Parser_Const.op_Or), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x || y))))))::uu____3439)
in (((FStar_Parser_Const.op_And), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x && y))))))::uu____3429)
in (((FStar_Parser_Const.op_Negation), ((Prims.parse_int "1")), ((unary_bool_op (fun x -> (not (x)))))))::uu____3419)
in (((FStar_Parser_Const.op_Modulus), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x mod y))))))::uu____3409)
in (((FStar_Parser_Const.op_GTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x >= y)))))))::uu____3399)
in (((FStar_Parser_Const.op_GT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x > y)))))))::uu____3389)
in (((FStar_Parser_Const.op_LTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x <= y)))))))::uu____3379)
in (((FStar_Parser_Const.op_LT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x < y)))))))::uu____3369)
in (((FStar_Parser_Const.op_Division), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x / y))))))::uu____3359)
in (((FStar_Parser_Const.op_Multiply), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x * y))))))::uu____3349)
in (((FStar_Parser_Const.op_Subtraction), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x - y))))))::uu____3339)
in (((FStar_Parser_Const.op_Addition), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x + y))))))::uu____3329)
in (((FStar_Parser_Const.op_Minus), ((Prims.parse_int "1")), ((unary_int_op (fun x -> (~- (x)))))))::uu____3319)
in (

let bounded_arith_ops = (

let bounded_int_types = ("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]
in (

let int_as_bounded = (fun r int_to_t1 n1 -> (

let c = (int_as_const r n1)
in (

let int_to_t2 = (FStar_Syntax_Syntax.fv_to_tm int_to_t1)
in (

let uu____3999 = (

let uu____4000 = (

let uu____4001 = (FStar_Syntax_Syntax.as_arg c)
in (uu____4001)::[])
in (FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____4000))
in (uu____3999 FStar_Pervasives_Native.None r)))))
in (FStar_All.pipe_right bounded_int_types (FStar_List.collect (fun m -> (

let uu____4028 = (

let uu____4037 = (FStar_Parser_Const.p2l (("FStar")::(m)::("add")::[]))
in ((uu____4037), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____4053 uu____4054 -> (match (((uu____4053), (uu____4054))) with
| ((int_to_t1, x), (uu____4065, y)) -> begin
(int_as_bounded r int_to_t1 (x + y))
end))))))
in (

let uu____4071 = (

let uu____4081 = (

let uu____4090 = (FStar_Parser_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((uu____4090), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____4106 uu____4107 -> (match (((uu____4106), (uu____4107))) with
| ((int_to_t1, x), (uu____4118, y)) -> begin
(int_as_bounded r int_to_t1 (x - y))
end))))))
in (

let uu____4124 = (

let uu____4134 = (

let uu____4143 = (FStar_Parser_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((uu____4143), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____4159 uu____4160 -> (match (((uu____4159), (uu____4160))) with
| ((int_to_t1, x), (uu____4171, y)) -> begin
(int_as_bounded r int_to_t1 (x * y))
end))))))
in (uu____4134)::[])
in (uu____4081)::uu____4124))
in (uu____4028)::uu____4071)))))))
in (FStar_List.map as_primitive_step (FStar_List.append basic_ops bounded_arith_ops)))))))))))))))))))))))))))))))))


let equality_ops : primitive_step Prims.list = (

let interp_prop = (fun r args -> (match (args) with
| ((_typ, uu____4236))::((a1, uu____4238))::((a2, uu____4240))::[] -> begin
(

let uu____4269 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____4269) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___169_4274 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___169_4274.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___169_4274.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___169_4274.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___170_4282 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___170_4282.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___170_4282.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___170_4282.FStar_Syntax_Syntax.vars}))
end
| uu____4287 -> begin
FStar_Pervasives_Native.None
end))
end
| ((_typ, uu____4289))::(uu____4290)::((a1, uu____4292))::((a2, uu____4294))::[] -> begin
(

let uu____4331 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____4331) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___169_4336 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___169_4336.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___169_4336.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___169_4336.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___170_4344 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___170_4344.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___170_4344.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___170_4344.FStar_Syntax_Syntax.vars}))
end
| uu____4349 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4350 -> begin
(failwith "Unexpected number of arguments")
end))
in (

let propositional_equality = {name = FStar_Parser_Const.eq2_lid; arity = (Prims.parse_int "3"); strong_reduction_ok = true; interpretation = interp_prop}
in (

let hetero_propositional_equality = {name = FStar_Parser_Const.eq3_lid; arity = (Prims.parse_int "4"); strong_reduction_ok = true; interpretation = interp_prop}
in (propositional_equality)::(hetero_propositional_equality)::[])))


let reduce_primops : cfg  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (

let uu____4362 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops cfg.steps))
in (match (uu____4362) with
| true -> begin
tm
end
| uu____4363 -> begin
(

let uu____4364 = (FStar_Syntax_Util.head_and_args tm)
in (match (uu____4364) with
| (head1, args) -> begin
(

let uu____4390 = (

let uu____4391 = (FStar_Syntax_Util.un_uinst head1)
in uu____4391.FStar_Syntax_Syntax.n)
in (match (uu____4390) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____4395 = (FStar_List.tryFind (fun ps -> (FStar_Syntax_Syntax.fv_eq_lid fv ps.name)) cfg.primitive_steps)
in (match (uu____4395) with
| FStar_Pervasives_Native.None -> begin
tm
end
| FStar_Pervasives_Native.Some (prim_step) -> begin
(match (((FStar_List.length args) < prim_step.arity)) with
| true -> begin
tm
end
| uu____4410 -> begin
(

let uu____4411 = (prim_step.interpretation head1.FStar_Syntax_Syntax.pos args)
in (match (uu____4411) with
| FStar_Pervasives_Native.None -> begin
tm
end
| FStar_Pervasives_Native.Some (reduced) -> begin
reduced
end))
end)
end))
end
| uu____4414 -> begin
tm
end))
end))
end)))


let reduce_equality : cfg  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (reduce_primops (

let uu___171_4425 = cfg
in {steps = (Primops)::[]; tcenv = uu___171_4425.tcenv; delta_level = uu___171_4425.delta_level; primitive_steps = equality_ops}) tm))


let maybe_simplify : cfg  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (

let steps = cfg.steps
in (

let w = (fun t -> (

let uu___172_4449 = t
in {FStar_Syntax_Syntax.n = uu___172_4449.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___172_4449.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___172_4449.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_Pervasives_Native.Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid) -> begin
FStar_Pervasives_Native.Some (false)
end
| uu____4468 -> begin
FStar_Pervasives_Native.None
end))
in (

let simplify = (fun arg -> (((simp_t (FStar_Pervasives_Native.fst arg))), (arg)))
in (

let tm1 = (reduce_primops cfg tm)
in (

let uu____4496 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps))
in (match (uu____4496) with
| true -> begin
tm1
end
| uu____4497 -> begin
(match (tm1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____4499; FStar_Syntax_Syntax.pos = uu____4500; FStar_Syntax_Syntax.vars = uu____4501}, uu____4502); FStar_Syntax_Syntax.tk = uu____4503; FStar_Syntax_Syntax.pos = uu____4504; FStar_Syntax_Syntax.vars = uu____4505}, args) -> begin
(

let uu____4525 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____4525) with
| true -> begin
(

let uu____4526 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____4526) with
| ((FStar_Pervasives_Native.Some (true), uu____4559))::((uu____4560, (arg, uu____4562)))::[] -> begin
arg
end
| ((uu____4603, (arg, uu____4605)))::((FStar_Pervasives_Native.Some (true), uu____4606))::[] -> begin
arg
end
| ((FStar_Pervasives_Native.Some (false), uu____4647))::(uu____4648)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____4686)::((FStar_Pervasives_Native.Some (false), uu____4687))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____4725 -> begin
tm1
end))
end
| uu____4734 -> begin
(

let uu____4735 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____4735) with
| true -> begin
(

let uu____4736 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____4736) with
| ((FStar_Pervasives_Native.Some (true), uu____4769))::(uu____4770)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____4808)::((FStar_Pervasives_Native.Some (true), uu____4809))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____4847))::((uu____4848, (arg, uu____4850)))::[] -> begin
arg
end
| ((uu____4891, (arg, uu____4893)))::((FStar_Pervasives_Native.Some (false), uu____4894))::[] -> begin
arg
end
| uu____4935 -> begin
tm1
end))
end
| uu____4944 -> begin
(

let uu____4945 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____4945) with
| true -> begin
(

let uu____4946 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____4946) with
| (uu____4979)::((FStar_Pervasives_Native.Some (true), uu____4980))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____5018))::(uu____5019)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____5057))::((uu____5058, (arg, uu____5060)))::[] -> begin
arg
end
| ((uu____5101, (p, uu____5103)))::((uu____5104, (q, uu____5106)))::[] -> begin
(

let uu____5148 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____5148) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____5149 -> begin
tm1
end))
end
| uu____5150 -> begin
tm1
end))
end
| uu____5159 -> begin
(

let uu____5160 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____5160) with
| true -> begin
(

let uu____5161 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____5161) with
| ((FStar_Pervasives_Native.Some (true), uu____5194))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____5218))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____5242 -> begin
tm1
end))
end
| uu____5251 -> begin
(

let uu____5252 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____5252) with
| true -> begin
(match (args) with
| ((t, uu____5254))::[] -> begin
(

let uu____5267 = (

let uu____5268 = (FStar_Syntax_Subst.compress t)
in uu____5268.FStar_Syntax_Syntax.n)
in (match (uu____5267) with
| FStar_Syntax_Syntax.Tm_abs ((uu____5271)::[], body, uu____5273) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____5289 -> begin
tm1
end)
end
| uu____5291 -> begin
tm1
end))
end
| ((uu____5292, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____5293))))::((t, uu____5295))::[] -> begin
(

let uu____5322 = (

let uu____5323 = (FStar_Syntax_Subst.compress t)
in uu____5323.FStar_Syntax_Syntax.n)
in (match (uu____5322) with
| FStar_Syntax_Syntax.Tm_abs ((uu____5326)::[], body, uu____5328) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____5344 -> begin
tm1
end)
end
| uu____5346 -> begin
tm1
end))
end
| uu____5347 -> begin
tm1
end)
end
| uu____5353 -> begin
(

let uu____5354 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____5354) with
| true -> begin
(match (args) with
| ((t, uu____5356))::[] -> begin
(

let uu____5369 = (

let uu____5370 = (FStar_Syntax_Subst.compress t)
in uu____5370.FStar_Syntax_Syntax.n)
in (match (uu____5369) with
| FStar_Syntax_Syntax.Tm_abs ((uu____5373)::[], body, uu____5375) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____5391 -> begin
tm1
end)
end
| uu____5393 -> begin
tm1
end))
end
| ((uu____5394, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____5395))))::((t, uu____5397))::[] -> begin
(

let uu____5424 = (

let uu____5425 = (FStar_Syntax_Subst.compress t)
in uu____5425.FStar_Syntax_Syntax.n)
in (match (uu____5424) with
| FStar_Syntax_Syntax.Tm_abs ((uu____5428)::[], body, uu____5430) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____5446 -> begin
tm1
end)
end
| uu____5448 -> begin
tm1
end))
end
| uu____5449 -> begin
tm1
end)
end
| uu____5455 -> begin
(reduce_equality cfg tm1)
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5457; FStar_Syntax_Syntax.pos = uu____5458; FStar_Syntax_Syntax.vars = uu____5459}, args) -> begin
(

let uu____5475 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____5475) with
| true -> begin
(

let uu____5476 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____5476) with
| ((FStar_Pervasives_Native.Some (true), uu____5509))::((uu____5510, (arg, uu____5512)))::[] -> begin
arg
end
| ((uu____5553, (arg, uu____5555)))::((FStar_Pervasives_Native.Some (true), uu____5556))::[] -> begin
arg
end
| ((FStar_Pervasives_Native.Some (false), uu____5597))::(uu____5598)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____5636)::((FStar_Pervasives_Native.Some (false), uu____5637))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____5675 -> begin
tm1
end))
end
| uu____5684 -> begin
(

let uu____5685 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____5685) with
| true -> begin
(

let uu____5686 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____5686) with
| ((FStar_Pervasives_Native.Some (true), uu____5719))::(uu____5720)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____5758)::((FStar_Pervasives_Native.Some (true), uu____5759))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____5797))::((uu____5798, (arg, uu____5800)))::[] -> begin
arg
end
| ((uu____5841, (arg, uu____5843)))::((FStar_Pervasives_Native.Some (false), uu____5844))::[] -> begin
arg
end
| uu____5885 -> begin
tm1
end))
end
| uu____5894 -> begin
(

let uu____5895 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____5895) with
| true -> begin
(

let uu____5896 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____5896) with
| (uu____5929)::((FStar_Pervasives_Native.Some (true), uu____5930))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____5968))::(uu____5969)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____6007))::((uu____6008, (arg, uu____6010)))::[] -> begin
arg
end
| ((uu____6051, (p, uu____6053)))::((uu____6054, (q, uu____6056)))::[] -> begin
(

let uu____6098 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____6098) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____6099 -> begin
tm1
end))
end
| uu____6100 -> begin
tm1
end))
end
| uu____6109 -> begin
(

let uu____6110 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____6110) with
| true -> begin
(

let uu____6111 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____6111) with
| ((FStar_Pervasives_Native.Some (true), uu____6144))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____6168))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____6192 -> begin
tm1
end))
end
| uu____6201 -> begin
(

let uu____6202 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____6202) with
| true -> begin
(match (args) with
| ((t, uu____6204))::[] -> begin
(

let uu____6217 = (

let uu____6218 = (FStar_Syntax_Subst.compress t)
in uu____6218.FStar_Syntax_Syntax.n)
in (match (uu____6217) with
| FStar_Syntax_Syntax.Tm_abs ((uu____6221)::[], body, uu____6223) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____6239 -> begin
tm1
end)
end
| uu____6241 -> begin
tm1
end))
end
| ((uu____6242, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6243))))::((t, uu____6245))::[] -> begin
(

let uu____6272 = (

let uu____6273 = (FStar_Syntax_Subst.compress t)
in uu____6273.FStar_Syntax_Syntax.n)
in (match (uu____6272) with
| FStar_Syntax_Syntax.Tm_abs ((uu____6276)::[], body, uu____6278) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____6294 -> begin
tm1
end)
end
| uu____6296 -> begin
tm1
end))
end
| uu____6297 -> begin
tm1
end)
end
| uu____6303 -> begin
(

let uu____6304 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____6304) with
| true -> begin
(match (args) with
| ((t, uu____6306))::[] -> begin
(

let uu____6319 = (

let uu____6320 = (FStar_Syntax_Subst.compress t)
in uu____6320.FStar_Syntax_Syntax.n)
in (match (uu____6319) with
| FStar_Syntax_Syntax.Tm_abs ((uu____6323)::[], body, uu____6325) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____6341 -> begin
tm1
end)
end
| uu____6343 -> begin
tm1
end))
end
| ((uu____6344, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6345))))::((t, uu____6347))::[] -> begin
(

let uu____6374 = (

let uu____6375 = (FStar_Syntax_Subst.compress t)
in uu____6375.FStar_Syntax_Syntax.n)
in (match (uu____6374) with
| FStar_Syntax_Syntax.Tm_abs ((uu____6378)::[], body, uu____6380) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____6396 -> begin
tm1
end)
end
| uu____6398 -> begin
tm1
end))
end
| uu____6399 -> begin
tm1
end)
end
| uu____6405 -> begin
(reduce_equality cfg tm1)
end))
end))
end))
end))
end))
end))
end
| uu____6406 -> begin
tm1
end)
end))))))))


let is_norm_request = (fun hd1 args -> (

let uu____6424 = (

let uu____6428 = (

let uu____6429 = (FStar_Syntax_Util.un_uinst hd1)
in uu____6429.FStar_Syntax_Syntax.n)
in ((uu____6428), (args)))
in (match (uu____6424) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____6434)::(uu____6435)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____6438)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize)
end
| uu____6440 -> begin
false
end)))


let get_norm_request = (fun args -> (match (args) with
| (uu____6462)::((tm, uu____6464))::[] -> begin
tm
end
| ((tm, uu____6474))::[] -> begin
tm
end
| uu____6479 -> begin
(failwith "Impossible")
end))


let is_reify_head : stack_elt Prims.list  ->  Prims.bool = (fun uu___144_6487 -> (match (uu___144_6487) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____6489; FStar_Syntax_Syntax.pos = uu____6490; FStar_Syntax_Syntax.vars = uu____6491}, uu____6492, uu____6493))::uu____6494 -> begin
true
end
| uu____6500 -> begin
false
end))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let firstn = (fun k l -> (match (((FStar_List.length l) < k)) with
| true -> begin
((l), ([]))
end
| uu____6612 -> begin
(FStar_Util.first_N k l)
end))
in ((log cfg (fun uu____6618 -> (

let uu____6619 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____6620 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6621 = (

let uu____6622 = (

let uu____6624 = (firstn (Prims.parse_int "4") stack1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6624))
in (stack_to_string uu____6622))
in (FStar_Util.print3 ">>> %s\nNorm %s with top of the stack %s \n" uu____6619 uu____6620 uu____6621))))));
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____6636) -> begin
(failwith "Impossible: got a delayed substitution")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____6651) when (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars)) -> begin
(

let uu____6662 = (

let uu____6663 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____6664 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s) CheckNoUvars: Unexpected unification variable remains: %s" uu____6663 uu____6664)))
in (failwith uu____6662))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.tk FStar_Pervasives_Native.None);
(rebuild cfg env stack1 t1);
)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____6669) -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.tk FStar_Pervasives_Native.None);
(rebuild cfg env stack1 t1);
)
end
| FStar_Syntax_Syntax.Tm_constant (uu____6684) -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.tk FStar_Pervasives_Native.None);
(rebuild cfg env stack1 t1);
)
end
| FStar_Syntax_Syntax.Tm_name (uu____6689) -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.tk FStar_Pervasives_Native.None);
(rebuild cfg env stack1 t1);
)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6694; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = uu____6695}) -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.tk FStar_Pervasives_Native.None);
(rebuild cfg env stack1 t1);
)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6701; FStar_Syntax_Syntax.fv_delta = uu____6702; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.tk FStar_Pervasives_Native.None);
(rebuild cfg env stack1 t1);
)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6707; FStar_Syntax_Syntax.fv_delta = uu____6708; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6709))}) -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.tk FStar_Pervasives_Native.None);
(rebuild cfg env stack1 t1);
)
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)) -> begin
(

let args1 = (closures_as_args_delayed cfg env args)
in (

let hd2 = (closure_as_term cfg env hd1)
in (

let t2 = (

let uu___173_6743 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd2), (args1))); FStar_Syntax_Syntax.tk = uu___173_6743.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___173_6743.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___173_6743.FStar_Syntax_Syntax.vars})
in ((FStar_ST.write t2.FStar_Syntax_Syntax.tk FStar_Pervasives_Native.None);
(rebuild cfg env stack1 t2);
))))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when (((

let uu____6775 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoFullNorm))
in (not (uu____6775))) && (is_norm_request hd1 args)) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid)))) -> begin
(

let tm = (get_norm_request args)
in (

let s = (Reify)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Primops)::[]
in (

let cfg' = (

let uu___174_6788 = cfg
in {steps = s; tcenv = uu___174_6788.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]; primitive_steps = uu___174_6788.primitive_steps})
in (

let stack' = (Debug (t1))::(Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (norm cfg' env stack' tm)))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____6793; FStar_Syntax_Syntax.pos = uu____6794; FStar_Syntax_Syntax.vars = uu____6795}, (a1)::(a2)::rest) -> begin
(

let uu____6829 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6829) with
| (hd1, uu____6840) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), ((a1)::[])))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (norm cfg env stack1 t2)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____6895)); FStar_Syntax_Syntax.tk = uu____6896; FStar_Syntax_Syntax.pos = uu____6897; FStar_Syntax_Syntax.vars = uu____6898}, (a)::[]) when ((FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) && (is_reify_head stack1)) -> begin
(

let uu____6921 = (FStar_List.tl stack1)
in (norm cfg env uu____6921 (FStar_Pervasives_Native.fst a)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____6924; FStar_Syntax_Syntax.pos = uu____6925; FStar_Syntax_Syntax.vars = uu____6926}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let uu____6949 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6949) with
| (reify_head, uu____6960) -> begin
(

let a1 = (

let uu____6976 = (FStar_All.pipe_left FStar_Syntax_Util.unascribe (FStar_Pervasives_Native.fst a))
in (FStar_Syntax_Subst.compress uu____6976))
in (match (a1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____6979)); FStar_Syntax_Syntax.tk = uu____6980; FStar_Syntax_Syntax.pos = uu____6981; FStar_Syntax_Syntax.vars = uu____6982}, (a2)::[]) -> begin
(norm cfg env stack1 (FStar_Pervasives_Native.fst a2))
end
| uu____7007 -> begin
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

let uu____7015 = (mk (FStar_Syntax_Syntax.Tm_type (u1)) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 uu____7015)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let uu____7022 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____7022) with
| true -> begin
(norm cfg env stack1 t')
end
| uu____7023 -> begin
(

let us1 = (

let uu____7025 = (

let uu____7029 = (FStar_List.map (norm_universe cfg env) us)
in ((uu____7029), (t1.FStar_Syntax_Syntax.pos)))
in UnivArgs (uu____7025))
in (

let stack2 = (us1)::stack1
in (norm cfg env stack2 t')))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t1
in (

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun uu___145_7039 -> (match (uu___145_7039) with
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

let uu____7042 = ((FStar_List.mem FStar_TypeChecker_Env.UnfoldTac cfg.delta_level) && (((((((((FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.and_lid) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.imp_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.forall_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.exists_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.eq2_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.true_lid)) || (FStar_Syntax_Syntax.fv_eq_lid f FStar_Parser_Const.false_lid)))
in (match (uu____7042) with
| true -> begin
false
end
| uu____7043 -> begin
should_delta
end))
in (match ((not (should_delta1))) with
| true -> begin
(rebuild cfg env stack1 t1)
end
| uu____7044 -> begin
(

let r_env = (

let uu____7046 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv uu____7046))
in (

let uu____7047 = (FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____7047) with
| FStar_Pervasives_Native.None -> begin
((log cfg (fun uu____7055 -> (FStar_Util.print "Tm_fvar case 2\n" [])));
(rebuild cfg env stack1 t1);
)
end
| FStar_Pervasives_Native.Some (us, t2) -> begin
((log cfg (fun uu____7064 -> (

let uu____7065 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____7066 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____7065 uu____7066)))));
(

let t3 = (

let uu____7068 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))))
in (match (uu____7068) with
| true -> begin
t2
end
| uu____7069 -> begin
(FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) t2)
end))
in (

let n1 = (FStar_List.length us)
in (match ((n1 > (Prims.parse_int "0"))) with
| true -> begin
(match (stack1) with
| (UnivArgs (us', uu____7080))::stack2 -> begin
(

let env1 = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env1 u -> (Univ (u))::env1) env))
in (norm cfg env1 stack2 t3))
end
| uu____7095 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack1 t3)
end
| uu____7096 -> begin
(

let uu____7097 = (

let uu____7098 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" uu____7098))
in (failwith uu____7097))
end)
end
| uu____7099 -> begin
(norm cfg env stack1 t3)
end)));
)
end)))
end))))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____7101 = (lookup_bvar env x)
in (match (uu____7101) with
| Univ (uu____7102) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env1, t0, r, fix) -> begin
(match (((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps))))) with
| true -> begin
(

let uu____7117 = (FStar_ST.read r)
in (match (uu____7117) with
| FStar_Pervasives_Native.Some (env2, t') -> begin
((log cfg (fun uu____7139 -> (

let uu____7140 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____7141 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" uu____7140 uu____7141)))));
(

let uu____7142 = (

let uu____7143 = (FStar_Syntax_Subst.compress t')
in uu____7143.FStar_Syntax_Syntax.n)
in (match (uu____7142) with
| FStar_Syntax_Syntax.Tm_abs (uu____7146) -> begin
(norm cfg env2 stack1 t')
end
| uu____7156 -> begin
(rebuild cfg env2 stack1 t')
end));
)
end
| FStar_Pervasives_Native.None -> begin
(norm cfg env1 ((MemoLazy (r))::stack1) t0)
end))
end
| uu____7163 -> begin
(norm cfg env1 stack1 t0)
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack1) with
| (UnivArgs (uu____7179))::uu____7180 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (uu____7185))::uu____7186 -> begin
(failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, uu____7192, uu____7193))::stack_rest -> begin
(match (c) with
| Univ (uu____7196) -> begin
(norm cfg ((c)::env) stack_rest t1)
end
| uu____7197 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (uu____7200)::[] -> begin
(match (lopt) with
| FStar_Pervasives_Native.None when (FStar_Options.__unit_tests ()) -> begin
((log cfg (fun uu____7210 -> (

let uu____7211 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____7211))));
(norm cfg ((c)::env) stack_rest body);
)
end
| FStar_Pervasives_Native.Some (rc) when (((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) || (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_Util.for_some (fun uu___146_7215 -> (match (uu___146_7215) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____7216 -> begin
false
end))))) -> begin
((log cfg (fun uu____7220 -> (

let uu____7221 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____7221))));
(norm cfg ((c)::env) stack_rest body);
)
end
| uu____7222 when ((FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) || (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| uu____7224 -> begin
(

let cfg1 = (

let uu___175_7227 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = uu___175_7227.tcenv; delta_level = uu___175_7227.delta_level; primitive_steps = uu___175_7227.primitive_steps})
in (

let uu____7228 = (closure_as_term cfg1 env t1)
in (rebuild cfg1 env stack1 uu____7228)))
end)
end
| (uu____7229)::tl1 -> begin
((log cfg (fun uu____7241 -> (

let uu____7242 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____7242))));
(

let body1 = (mk (FStar_Syntax_Syntax.Tm_abs (((tl1), (body), (lopt)))) t1.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body1));
)
end)
end)
end
| (Steps (s, ps, dl))::stack2 -> begin
(norm (

let uu___176_7263 = cfg
in {steps = s; tcenv = uu___176_7263.tcenv; delta_level = dl; primitive_steps = ps}) env stack2 t1)
end
| (MemoLazy (r))::stack2 -> begin
((set_memo r ((env), (t1)));
(log cfg (fun uu____7278 -> (

let uu____7279 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____7279))));
(norm cfg env stack2 t1);
)
end
| (Debug (uu____7280))::uu____7281 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7283 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7283))
end
| uu____7284 -> begin
(

let uu____7285 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7285) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7301 -> (Dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____7311 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____7311) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____7320 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____7320))))
end
| uu____7321 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___177_7325 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___177_7325.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___177_7325.FStar_Syntax_Syntax.residual_flags})))
end
| uu____7326 -> begin
lopt
end)
in ((log cfg (fun uu____7331 -> (

let uu____7332 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7332))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___178_7344 = cfg
in (

let uu____7345 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___178_7344.steps; tcenv = uu___178_7344.tcenv; delta_level = uu___178_7344.delta_level; primitive_steps = uu____7345}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Meta (uu____7351))::uu____7352 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7356 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7356))
end
| uu____7357 -> begin
(

let uu____7358 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7358) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7374 -> (Dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____7384 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____7384) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____7393 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____7393))))
end
| uu____7394 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___177_7398 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___177_7398.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___177_7398.FStar_Syntax_Syntax.residual_flags})))
end
| uu____7399 -> begin
lopt
end)
in ((log cfg (fun uu____7404 -> (

let uu____7405 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7405))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___178_7417 = cfg
in (

let uu____7418 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___178_7417.steps; tcenv = uu___178_7417.tcenv; delta_level = uu___178_7417.delta_level; primitive_steps = uu____7418}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Let (uu____7424))::uu____7425 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7431 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7431))
end
| uu____7432 -> begin
(

let uu____7433 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7433) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7449 -> (Dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____7459 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____7459) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____7468 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____7468))))
end
| uu____7469 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___177_7473 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___177_7473.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___177_7473.FStar_Syntax_Syntax.residual_flags})))
end
| uu____7474 -> begin
lopt
end)
in ((log cfg (fun uu____7479 -> (

let uu____7480 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7480))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___178_7492 = cfg
in (

let uu____7493 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___178_7492.steps; tcenv = uu___178_7492.tcenv; delta_level = uu___178_7492.delta_level; primitive_steps = uu____7493}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (App (uu____7499))::uu____7500 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7505 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7505))
end
| uu____7506 -> begin
(

let uu____7507 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7507) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7523 -> (Dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____7533 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____7533) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____7542 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____7542))))
end
| uu____7543 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___177_7547 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___177_7547.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___177_7547.FStar_Syntax_Syntax.residual_flags})))
end
| uu____7548 -> begin
lopt
end)
in ((log cfg (fun uu____7553 -> (

let uu____7554 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7554))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___178_7566 = cfg
in (

let uu____7567 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___178_7566.steps; tcenv = uu___178_7566.tcenv; delta_level = uu___178_7566.delta_level; primitive_steps = uu____7567}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Abs (uu____7573))::uu____7574 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7582 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7582))
end
| uu____7583 -> begin
(

let uu____7584 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7584) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7600 -> (Dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____7610 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____7610) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____7619 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____7619))))
end
| uu____7620 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___177_7624 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___177_7624.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___177_7624.FStar_Syntax_Syntax.residual_flags})))
end
| uu____7625 -> begin
lopt
end)
in ((log cfg (fun uu____7630 -> (

let uu____7631 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7631))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___178_7643 = cfg
in (

let uu____7644 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___178_7643.steps; tcenv = uu___178_7643.tcenv; delta_level = uu___178_7643.delta_level; primitive_steps = uu____7644}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| [] -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7650 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7650))
end
| uu____7651 -> begin
(

let uu____7652 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7652) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7668 -> (Dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (

let uu____7678 = (FStar_All.pipe_right cfg.steps (FStar_List.contains CheckNoUvars))
in (match (uu____7678) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____7687 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____7687))))
end
| uu____7688 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end))
in FStar_Pervasives_Native.Some ((

let uu___177_7692 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___177_7692.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___177_7692.FStar_Syntax_Syntax.residual_flags})))
end
| uu____7693 -> begin
lopt
end)
in ((log cfg (fun uu____7698 -> (

let uu____7699 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7699))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___178_7711 = cfg
in (

let uu____7712 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___178_7711.steps; tcenv = uu___178_7711.tcenv; delta_level = uu___178_7711.delta_level; primitive_steps = uu____7712}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack2 = (FStar_All.pipe_right stack1 (FStar_List.fold_right (fun uu____7745 stack2 -> (match (uu____7745) with
| (a, aq) -> begin
(

let uu____7753 = (

let uu____7754 = (

let uu____7758 = (

let uu____7759 = (

let uu____7769 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____7769), (false)))
in Clos (uu____7759))
in ((uu____7758), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____7754))
in (uu____7753)::stack2)
end)) args))
in ((log cfg (fun uu____7793 -> (

let uu____7794 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____7794))));
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

let uu___179_7818 = x
in {FStar_Syntax_Syntax.ppname = uu___179_7818.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___179_7818.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 t2)))
end
| uu____7819 -> begin
(

let uu____7822 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7822))
end)
end
| uu____7823 -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let uu____7825 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____7825) with
| (closing, f1) -> begin
(

let f2 = (norm cfg ((Dummy)::env) [] f1)
in (

let t2 = (

let uu____7841 = (

let uu____7842 = (

let uu____7847 = (FStar_Syntax_Subst.close closing f2)
in (((

let uu___180_7849 = x
in {FStar_Syntax_Syntax.ppname = uu___180_7849.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___180_7849.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (uu____7847)))
in FStar_Syntax_Syntax.Tm_refine (uu____7842))
in (mk uu____7841 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack1 t2)))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7862 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7862))
end
| uu____7863 -> begin
(

let uu____7864 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7864) with
| (bs1, c1) -> begin
(

let c2 = (

let uu____7870 = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7878 -> (Dummy)::env1) env))
in (norm_comp cfg uu____7870 c1))
in (

let t2 = (

let uu____7885 = (norm_binders cfg env bs1)
in (FStar_Syntax_Util.arrow uu____7885 c2))
in (rebuild cfg env stack1 t2)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) -> begin
(match (stack1) with
| (Match (uu____7928))::uu____7929 -> begin
(norm cfg env stack1 t11)
end
| (Arg (uu____7934))::uu____7935 -> begin
(norm cfg env stack1 t11)
end
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____7940; FStar_Syntax_Syntax.pos = uu____7941; FStar_Syntax_Syntax.vars = uu____7942}, uu____7943, uu____7944))::uu____7945 -> begin
(norm cfg env stack1 t11)
end
| (MemoLazy (uu____7951))::uu____7952 -> begin
(norm cfg env stack1 t11)
end
| uu____7957 -> begin
(

let t12 = (norm cfg env [] t11)
in ((log cfg (fun uu____7961 -> (FStar_Util.print_string "+++ Normalizing ascription \n")));
(

let tc1 = (match (tc) with
| FStar_Util.Inl (t2) -> begin
(

let uu____7974 = (norm cfg env [] t2)
in FStar_Util.Inl (uu____7974))
end
| FStar_Util.Inr (c) -> begin
(

let uu____7982 = (norm_comp cfg env c)
in FStar_Util.Inr (uu____7982))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (norm cfg env []))
in (

let uu____7987 = (

let uu____7988 = (

let uu____7989 = (

let uu____8007 = (FStar_Syntax_Util.unascribe t12)
in ((uu____8007), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____7989))
in (mk uu____7988 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack1 uu____7987))));
))
end)
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let stack2 = (Match (((env), (branches), (t1.FStar_Syntax_Syntax.pos))))::stack1
in (norm cfg env stack2 head1))
end
| FStar_Syntax_Syntax.Tm_let ((uu____8055, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____8056); FStar_Syntax_Syntax.lbunivs = uu____8057; FStar_Syntax_Syntax.lbtyp = uu____8058; FStar_Syntax_Syntax.lbeff = uu____8059; FStar_Syntax_Syntax.lbdef = uu____8060})::uu____8061), uu____8062) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n1 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in (

let uu____8088 = ((

let uu____8091 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps))
in (not (uu____8091))) && ((FStar_Syntax_Util.is_pure_effect n1) || ((FStar_Syntax_Util.is_ghost_effect n1) && (

let uu____8093 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (not (uu____8093))))))
in (match (uu____8088) with
| true -> begin
(

let env1 = (

let uu____8096 = (

let uu____8097 = (

let uu____8107 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (uu____8107), (false)))
in Clos (uu____8097))
in (uu____8096)::env)
in (norm cfg env1 stack1 body))
end
| uu____8130 -> begin
(

let uu____8131 = (

let uu____8134 = (

let uu____8135 = (

let uu____8136 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right uu____8136 FStar_Syntax_Syntax.mk_binder))
in (uu____8135)::[])
in (FStar_Syntax_Subst.open_term uu____8134 body))
in (match (uu____8131) with
| (bs, body1) -> begin
(

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let x = (

let uu____8146 = (FStar_List.hd bs)
in (FStar_Pervasives_Native.fst uu____8146))
in FStar_Util.Inl ((

let uu___181_8152 = x
in {FStar_Syntax_Syntax.ppname = uu___181_8152.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___181_8152.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
in (

let lb1 = (

let uu___182_8154 = lb
in (

let uu____8155 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___182_8154.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___182_8154.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____8155}))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env1 uu____8167 -> (Dummy)::env1) env))
in (norm cfg env' ((Let (((env), (bs), (lb1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), body) when (FStar_List.contains CompressUvars cfg.steps) -> begin
(

let uu____8182 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____8182) with
| (lbs1, body1) -> begin
(

let lbs2 = (FStar_List.map (fun lb -> (

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let uu____8210 = (

let uu___183_8211 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___183_8211.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___183_8211.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})
in FStar_Util.Inl (uu____8210))
in (

let uu____8212 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____8212) with
| (xs, def_body, lopt) -> begin
(

let xs1 = (norm_binders cfg env xs)
in (

let env1 = (

let uu____8225 = (FStar_List.map (fun uu____8228 -> Dummy) lbs1)
in (

let uu____8229 = (

let uu____8231 = (FStar_List.map (fun uu____8236 -> Dummy) xs1)
in (FStar_List.append uu____8231 env))
in (FStar_List.append uu____8225 uu____8229)))
in (

let def_body1 = (norm cfg env1 [] def_body)
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____8244 = (

let uu___184_8245 = rc
in (

let uu____8246 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env1 []))
in {FStar_Syntax_Syntax.residual_effect = uu___184_8245.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____8246; FStar_Syntax_Syntax.residual_flags = uu___184_8245.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____8244))
end
| uu____8252 -> begin
lopt
end)
in (

let def = (FStar_Syntax_Util.abs xs1 def_body1 lopt1)
in (

let uu___185_8255 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___185_8255.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___185_8255.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def}))))))
end))))) lbs1)
in (

let env' = (

let uu____8258 = (FStar_List.map (fun uu____8261 -> Dummy) lbs2)
in (FStar_List.append uu____8258 env))
in (

let body2 = (norm cfg env' [] body1)
in (

let uu____8263 = (FStar_Syntax_Subst.close_let_rec lbs2 body2)
in (match (uu____8263) with
| (lbs3, body3) -> begin
(

let t2 = (

let uu___186_8274 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (body3))); FStar_Syntax_Syntax.tk = uu___186_8274.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___186_8274.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___186_8274.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack1 t2))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(

let uu____8295 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____8295))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let uu____8308 = (FStar_List.fold_right (fun lb uu____8339 -> (match (uu____8339) with
| (rec_env, memos, i) -> begin
(

let f_i = (

let uu____8378 = (

let uu___187_8379 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___187_8379.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___187_8379.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm uu____8378))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t1.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let rec_env1 = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env1), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (FStar_Pervasives_Native.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (uu____8308) with
| (rec_env, memos, uu____8439) -> begin
(

let uu____8454 = (FStar_List.map2 (fun lb memo -> (FStar_ST.write memo (FStar_Pervasives_Native.Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (FStar_Pervasives_Native.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env1 -> (

let uu____8501 = (

let uu____8502 = (

let uu____8512 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (uu____8512), (false)))
in Clos (uu____8502))
in (uu____8501)::env1)) (FStar_Pervasives_Native.snd lbs) env)
in (norm cfg body_env stack1 body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head1, m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m1, t2) -> begin
(

let should_reify = (match (stack1) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____8550; FStar_Syntax_Syntax.pos = uu____8551; FStar_Syntax_Syntax.vars = uu____8552}, uu____8553, uu____8554))::uu____8555 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____8561 -> begin
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

let uu____8568 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____8568) with
| true -> begin
(

let uu___188_8569 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::(NoDeltaSteps)::[]; tcenv = uu___188_8569.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___188_8569.primitive_steps})
end
| uu____8570 -> begin
(

let uu___189_8571 = cfg
in {steps = (FStar_List.append ((NoDeltaSteps)::(Exclude (Zeta))::[]) cfg.steps); tcenv = uu___189_8571.tcenv; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___189_8571.primitive_steps})
end))
in (norm cfg1 env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m1), (t3)))), (t3.FStar_Syntax_Syntax.pos))))::stack2) head1))))
end
| uu____8572 -> begin
(

let uu____8573 = (

let uu____8574 = (FStar_Syntax_Subst.compress head1)
in uu____8574.FStar_Syntax_Syntax.n)
in (match (uu____8573) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m1)
in (

let uu____8588 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____8588) with
| (uu____8589, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____8593) -> begin
(failwith "Cannot reify a top-level let binding")
end
| FStar_Util.Inl (x) -> begin
(

let is_return = (fun e -> (

let uu____8600 = (

let uu____8601 = (FStar_Syntax_Subst.compress e)
in uu____8601.FStar_Syntax_Syntax.n)
in (match (uu____8600) with
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____8606, uu____8607)) -> begin
(

let uu____8616 = (

let uu____8617 = (FStar_Syntax_Subst.compress e1)
in uu____8617.FStar_Syntax_Syntax.n)
in (match (uu____8616) with
| FStar_Syntax_Syntax.Tm_meta (e2, FStar_Syntax_Syntax.Meta_monadic_lift (uu____8622, msrc, uu____8624)) when (FStar_Syntax_Util.is_pure_effect msrc) -> begin
(

let uu____8633 = (FStar_Syntax_Subst.compress e2)
in FStar_Pervasives_Native.Some (uu____8633))
end
| uu____8634 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____8635 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____8636 = (is_return lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____8636) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let lb1 = (

let uu___190_8640 = lb
in {FStar_Syntax_Syntax.lbname = uu___190_8640.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___190_8640.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___190_8640.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = e})
in (

let uu____8641 = (FStar_List.tl stack1)
in (

let uu____8642 = (

let uu____8643 = (

let uu____8646 = (

let uu____8647 = (

let uu____8655 = (FStar_Syntax_Util.mk_reify body)
in ((((false), ((lb1)::[]))), (uu____8655)))
in FStar_Syntax_Syntax.Tm_let (uu____8647))
in (FStar_Syntax_Syntax.mk uu____8646))
in (uu____8643 FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos))
in (norm cfg env uu____8641 uu____8642))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8672 = (

let uu____8673 = (is_return body)
in (match (uu____8673) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_bvar (y); FStar_Syntax_Syntax.tk = uu____8676; FStar_Syntax_Syntax.pos = uu____8677; FStar_Syntax_Syntax.vars = uu____8678}) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____8683 -> begin
false
end))
in (match (uu____8672) with
| true -> begin
(norm cfg env stack1 lb.FStar_Syntax_Syntax.lbdef)
end
| uu____8685 -> begin
(

let head2 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body1 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify body)
in (

let body_rc = {FStar_Syntax_Syntax.residual_effect = m1; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t2); FStar_Syntax_Syntax.residual_flags = []}
in (

let body2 = (

let uu____8706 = (

let uu____8709 = (

let uu____8710 = (

let uu____8720 = (

let uu____8722 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____8722)::[])
in ((uu____8720), (body1), (FStar_Pervasives_Native.Some (body_rc))))
in FStar_Syntax_Syntax.Tm_abs (uu____8710))
in (FStar_Syntax_Syntax.mk uu____8709))
in (uu____8706 FStar_Pervasives_Native.None body1.FStar_Syntax_Syntax.pos))
in (

let close1 = (closure_as_term cfg env)
in (

let bind_inst = (

let uu____8741 = (

let uu____8742 = (FStar_Syntax_Subst.compress bind_repr)
in uu____8742.FStar_Syntax_Syntax.n)
in (match (uu____8741) with
| FStar_Syntax_Syntax.Tm_uinst (bind1, (uu____8748)::(uu____8749)::[]) -> begin
(

let uu____8755 = (

let uu____8758 = (

let uu____8759 = (

let uu____8764 = (

let uu____8766 = (

let uu____8767 = (close1 lb.FStar_Syntax_Syntax.lbtyp)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____8767))
in (

let uu____8768 = (

let uu____8770 = (

let uu____8771 = (close1 t2)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____8771))
in (uu____8770)::[])
in (uu____8766)::uu____8768))
in ((bind1), (uu____8764)))
in FStar_Syntax_Syntax.Tm_uinst (uu____8759))
in (FStar_Syntax_Syntax.mk uu____8758))
in (uu____8755 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
end
| uu____8783 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let reified = (

let uu____8789 = (

let uu____8792 = (

let uu____8793 = (

let uu____8803 = (

let uu____8805 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____8806 = (

let uu____8808 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____8809 = (

let uu____8811 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____8812 = (

let uu____8814 = (FStar_Syntax_Syntax.as_arg head2)
in (

let uu____8815 = (

let uu____8817 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____8818 = (

let uu____8820 = (FStar_Syntax_Syntax.as_arg body2)
in (uu____8820)::[])
in (uu____8817)::uu____8818))
in (uu____8814)::uu____8815))
in (uu____8811)::uu____8812))
in (uu____8808)::uu____8809))
in (uu____8805)::uu____8806))
in ((bind_inst), (uu____8803)))
in FStar_Syntax_Syntax.Tm_app (uu____8793))
in (FStar_Syntax_Syntax.mk uu____8792))
in (uu____8789 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (

let uu____8832 = (FStar_List.tl stack1)
in (norm cfg env uu____8832 reified)))))))))
end))
end)))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head_app, args) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m1)
in (

let uu____8850 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____8850) with
| (uu____8851, bind_repr) -> begin
(

let maybe_unfold_action = (fun head2 -> (

let maybe_extract_fv = (fun t3 -> (

let t4 = (

let uu____8874 = (

let uu____8875 = (FStar_Syntax_Subst.compress t3)
in uu____8875.FStar_Syntax_Syntax.n)
in (match (uu____8874) with
| FStar_Syntax_Syntax.Tm_uinst (t4, uu____8881) -> begin
t4
end
| uu____8886 -> begin
head2
end))
in (

let uu____8887 = (

let uu____8888 = (FStar_Syntax_Subst.compress t4)
in uu____8888.FStar_Syntax_Syntax.n)
in (match (uu____8887) with
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____8893 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____8894 = (maybe_extract_fv head2)
in (match (uu____8894) with
| FStar_Pervasives_Native.Some (x) when (

let uu____8900 = (FStar_Syntax_Syntax.lid_of_fv x)
in (FStar_TypeChecker_Env.is_action cfg.tcenv uu____8900)) -> begin
(

let head3 = (norm cfg env [] head2)
in (

let action_unfolded = (

let uu____8904 = (maybe_extract_fv head3)
in (match (uu____8904) with
| FStar_Pervasives_Native.Some (uu____8907) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____8908 -> begin
FStar_Pervasives_Native.Some (false)
end))
in ((head3), (action_unfolded))))
end
| uu____8911 -> begin
((head2), (FStar_Pervasives_Native.None))
end))))
in ((

let is_arg_impure = (fun uu____8922 -> (match (uu____8922) with
| (e, q) -> begin
(

let uu____8927 = (

let uu____8928 = (FStar_Syntax_Subst.compress e)
in uu____8928.FStar_Syntax_Syntax.n)
in (match (uu____8927) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m11, m2, t')) -> begin
(not ((FStar_Syntax_Util.is_pure_effect m11)))
end
| uu____8943 -> begin
false
end))
end))
in (

let uu____8944 = (

let uu____8945 = (

let uu____8949 = (FStar_Syntax_Syntax.as_arg head_app)
in (uu____8949)::args)
in (FStar_Util.for_some is_arg_impure uu____8945))
in (match (uu____8944) with
| true -> begin
(

let uu____8952 = (

let uu____8953 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format1 "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n" uu____8953))
in (failwith uu____8952))
end
| uu____8954 -> begin
()
end)));
(

let uu____8955 = (maybe_unfold_action head_app)
in (match (uu____8955) with
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

let uu____8990 = (FStar_List.tl stack1)
in (norm cfg env uu____8990 body1)))))
end));
))
end)))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (

let uu____9004 = (closure_as_term cfg env t')
in (reify_lift cfg.tcenv e msrc mtgt uu____9004))
in (

let uu____9005 = (FStar_List.tl stack1)
in (norm cfg env uu____9005 lifted)))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____9086 -> (match (uu____9086) with
| (pat, wopt, tm) -> begin
(

let uu____9120 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____9120)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches1)))) t2.FStar_Syntax_Syntax.pos)
in (

let uu____9144 = (FStar_List.tl stack1)
in (norm cfg env uu____9144 tm))))
end
| uu____9145 -> begin
(norm cfg env stack1 head1)
end))
end))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) -> begin
(

let should_reify = (match (stack1) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____9154; FStar_Syntax_Syntax.pos = uu____9155; FStar_Syntax_Syntax.vars = uu____9156}, uu____9157, uu____9158))::uu____9159 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____9165 -> begin
false
end)
in (match (should_reify) with
| true -> begin
(

let uu____9166 = (FStar_List.tl stack1)
in (

let uu____9167 = (

let uu____9168 = (closure_as_term cfg env t2)
in (reify_lift cfg.tcenv head1 m1 m' uu____9168))
in (norm cfg env uu____9166 uu____9167)))
end
| uu____9169 -> begin
(

let t3 = (norm cfg env [] t2)
in (

let uu____9171 = (((FStar_Syntax_Util.is_pure_effect m1) || (FStar_Syntax_Util.is_ghost_effect m1)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)))
in (match (uu____9171) with
| true -> begin
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___191_9177 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = uu___191_9177.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___191_9177.primitive_steps})
in (norm cfg1 env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t3)))), (head1.FStar_Syntax_Syntax.pos))))::stack2) head1)))
end
| uu____9178 -> begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t3)))), (head1.FStar_Syntax_Syntax.pos))))::stack1) head1)
end)))
end))
end
| uu____9179 -> begin
(match (stack1) with
| (uu____9180)::uu____9181 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____9185) -> begin
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
| uu____9202 -> begin
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

let uu____9212 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (uu____9212))
end
| uu____9219 -> begin
m
end)
in (

let t2 = (mk (FStar_Syntax_Syntax.Tm_meta (((head2), (m1)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 t2))))
end)
end)
end);
))))
and reify_lift : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env e msrc mtgt t -> (match ((FStar_Syntax_Util.is_pure_effect msrc)) with
| true -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl env mtgt)
in (

let uu____9231 = ed.FStar_Syntax_Syntax.return_repr
in (match (uu____9231) with
| (uu____9232, return_repr) -> begin
(

let return_inst = (

let uu____9239 = (

let uu____9240 = (FStar_Syntax_Subst.compress return_repr)
in uu____9240.FStar_Syntax_Syntax.n)
in (match (uu____9239) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (uu____9246)::[]) -> begin
(

let uu____9252 = (

let uu____9255 = (

let uu____9256 = (

let uu____9261 = (

let uu____9263 = (env.FStar_TypeChecker_Env.universe_of env t)
in (uu____9263)::[])
in ((return_tm), (uu____9261)))
in FStar_Syntax_Syntax.Tm_uinst (uu____9256))
in (FStar_Syntax_Syntax.mk uu____9255))
in (uu____9252 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end
| uu____9275 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let uu____9278 = (

let uu____9281 = (

let uu____9282 = (

let uu____9292 = (

let uu____9294 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____9295 = (

let uu____9297 = (FStar_Syntax_Syntax.as_arg e)
in (uu____9297)::[])
in (uu____9294)::uu____9295))
in ((return_inst), (uu____9292)))
in FStar_Syntax_Syntax.Tm_app (uu____9282))
in (FStar_Syntax_Syntax.mk uu____9281))
in (uu____9278 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end)))
end
| uu____9309 -> begin
(

let uu____9310 = (FStar_TypeChecker_Env.monad_leq env msrc mtgt)
in (match (uu____9310) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9312 = (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" (FStar_Ident.text_of_lid msrc) (FStar_Ident.text_of_lid mtgt))
in (failwith uu____9312))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____9313; FStar_TypeChecker_Env.mtarget = uu____9314; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____9315; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(failwith "Impossible : trying to reify a non-reifiable lift (from %s to %s)")
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____9326; FStar_TypeChecker_Env.mtarget = uu____9327; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____9328; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let uu____9346 = (FStar_Syntax_Util.mk_reify e)
in (lift t FStar_Syntax_Syntax.tun uu____9346))
end))
end))
and norm_pattern_args : cfg  ->  env  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun uu____9380 -> (match (uu____9380) with
| (a, imp) -> begin
(

let uu____9387 = (norm cfg env [] a)
in ((uu____9387), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp1 = (ghost_to_pure_aux cfg env comp)
in (match (comp1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu___192_9402 = comp1
in (

let uu____9405 = (

let uu____9406 = (

let uu____9412 = (norm cfg env [] t)
in (

let uu____9413 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____9412), (uu____9413))))
in FStar_Syntax_Syntax.Total (uu____9406))
in {FStar_Syntax_Syntax.n = uu____9405; FStar_Syntax_Syntax.tk = uu___192_9402.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___192_9402.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___192_9402.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu___193_9428 = comp1
in (

let uu____9431 = (

let uu____9432 = (

let uu____9438 = (norm cfg env [] t)
in (

let uu____9439 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____9438), (uu____9439))))
in FStar_Syntax_Syntax.GTotal (uu____9432))
in {FStar_Syntax_Syntax.n = uu____9431; FStar_Syntax_Syntax.tk = uu___193_9428.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___193_9428.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___193_9428.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____9474 -> (match (uu____9474) with
| (a, i) -> begin
(

let uu____9481 = (norm cfg env [] a)
in ((uu____9481), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___147_9489 -> (match (uu___147_9489) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____9493 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____9493))
end
| f -> begin
f
end))))
in (

let uu___194_9497 = comp1
in (

let uu____9500 = (

let uu____9501 = (

let uu___195_9502 = ct
in (

let uu____9503 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (

let uu____9504 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____9507 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = uu____9503; FStar_Syntax_Syntax.effect_name = uu___195_9502.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____9504; FStar_Syntax_Syntax.effect_args = uu____9507; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (uu____9501))
in {FStar_Syntax_Syntax.n = uu____9500; FStar_Syntax_Syntax.tk = uu___194_9497.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___194_9497.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___194_9497.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm1 = (fun t -> (norm (

let uu___196_9526 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = uu___196_9526.tcenv; delta_level = uu___196_9526.delta_level; primitive_steps = uu___196_9526.primitive_steps}) env [] t))
in (

let non_info = (fun t -> (

let uu____9531 = (norm1 t)
in (FStar_Syntax_Util.non_informative uu____9531)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____9534) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let uu___197_9548 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = uu___197_9548.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___197_9548.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___197_9548.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____9558 = ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ))
in (match (uu____9558) with
| true -> begin
(

let ct1 = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let flags = (match ((FStar_Ident.lid_equals pure_eff FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::ct.FStar_Syntax_Syntax.flags
end
| uu____9566 -> begin
ct.FStar_Syntax_Syntax.flags
end)
in (

let uu___198_9567 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___198_9567.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = uu___198_9567.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___198_9567.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags}))
end
| FStar_Pervasives_Native.None -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c)
in (

let uu___199_9569 = ct1
in {FStar_Syntax_Syntax.comp_univs = uu___199_9569.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu___199_9569.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___199_9569.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___199_9569.FStar_Syntax_Syntax.flags}))
end)
in (

let uu___200_9570 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.tk = uu___200_9570.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___200_9570.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___200_9570.FStar_Syntax_Syntax.vars}))
end
| uu____9575 -> begin
c
end)))
end
| uu____9576 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env uu____9579 -> (match (uu____9579) with
| (x, imp) -> begin
(

let uu____9582 = (

let uu___201_9583 = x
in (

let uu____9584 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___201_9583.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___201_9583.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____9584}))
in ((uu____9582), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let uu____9590 = (FStar_List.fold_left (fun uu____9602 b -> (match (uu____9602) with
| (nbs', env1) -> begin
(

let b1 = (norm_binder cfg env1 b)
in (((b1)::nbs'), ((Dummy)::env1)))
end)) (([]), (env)) bs)
in (match (uu____9590) with
| (nbs, uu____9619) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags = (filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags)
in (

let uu____9630 = (

let uu___202_9631 = rc
in (

let uu____9632 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___202_9631.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____9632; FStar_Syntax_Syntax.residual_flags = uu___202_9631.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____9630)))
end
| uu____9638 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 t -> (match (stack1) with
| [] -> begin
t
end
| (Debug (tm))::stack2 -> begin
((

let uu____9648 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms")))
in (match (uu____9648) with
| true -> begin
(

let uu____9649 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____9650 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Normalized %s to %s\n" uu____9649 uu____9650)))
end
| uu____9651 -> begin
()
end));
(rebuild cfg env stack2 t);
)
end
| (Steps (s, ps, dl))::stack2 -> begin
(rebuild (

let uu___203_9663 = cfg
in {steps = s; tcenv = uu___203_9663.tcenv; delta_level = dl; primitive_steps = ps}) env stack2 t)
end
| (Meta (m, r))::stack2 -> begin
(

let t1 = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack2 t1))
end
| (MemoLazy (r))::stack2 -> begin
((set_memo r ((env), (t)));
(log cfg (fun uu____9685 -> (

let uu____9686 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" uu____9686))));
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

let uu____9717 = (

let uu___204_9718 = (FStar_Syntax_Util.abs bs1 t lopt1)
in {FStar_Syntax_Syntax.n = uu___204_9718.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___204_9718.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___204_9718.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack2 uu____9717))))
end
| (Arg (Univ (uu____9723), uu____9724, uu____9725))::uu____9726 -> begin
(failwith "Impossible")
end
| (Arg (Dummy, uu____9728, uu____9729))::uu____9730 -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack2 -> begin
(

let t1 = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack2 t1))
end
| (Arg (Clos (env1, tm, m, uu____9742), aq, r))::stack2 -> begin
((log cfg (fun uu____9760 -> (

let uu____9761 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" uu____9761))));
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
| uu____9768 -> begin
(

let stack3 = (App (((t), (aq), (r))))::stack2
in (norm cfg env1 stack3 tm))
end)
end
| uu____9771 -> begin
(

let uu____9772 = (FStar_ST.read m)
in (match (uu____9772) with
| FStar_Pervasives_Native.None -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let arg = (closure_as_term cfg env1 tm)
in (

let t1 = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack2 t1)))
end
| uu____9792 -> begin
(

let stack3 = (MemoLazy (m))::(App (((t), (aq), (r))))::stack2
in (norm cfg env1 stack3 tm))
end)
end
| FStar_Pervasives_Native.Some (uu____9798, a) -> begin
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

let uu____9820 = (maybe_simplify cfg t1)
in (rebuild cfg env stack2 uu____9820)))
end
| (Match (env1, branches, r))::stack2 -> begin
((log cfg (fun uu____9829 -> (

let uu____9830 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" uu____9830))));
(

let scrutinee = t
in (

let norm_and_rebuild_match = (fun uu____9835 -> ((log cfg (fun uu____9840 -> (

let uu____9841 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____9842 = (

let uu____9843 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____9854 -> (match (uu____9854) with
| (p, uu____9860, uu____9861) -> begin
(FStar_Syntax_Print.pat_to_string p)
end))))
in (FStar_All.pipe_right uu____9843 (FStar_String.concat "\n\t")))
in (FStar_Util.print2 "match is irreducible: scrutinee=%s\nbranches=%s\n" uu____9841 uu____9842)))));
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg_exclude_iota_zeta = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun uu___148_9872 -> (match (uu___148_9872) with
| FStar_TypeChecker_Env.Inlining -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| uu____9873 -> begin
false
end))))
in (

let steps' = (

let uu____9876 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____9876) with
| true -> begin
(Exclude (Zeta))::[]
end
| uu____9878 -> begin
(Exclude (Iota))::(Exclude (Zeta))::[]
end))
in (

let uu___205_9879 = cfg
in {steps = (FStar_List.append steps' cfg.steps); tcenv = uu___205_9879.tcenv; delta_level = new_delta; primitive_steps = uu___205_9879.primitive_steps})))
in (

let norm_or_whnf = (fun env2 t1 -> (match (whnf) with
| true -> begin
(closure_as_term cfg_exclude_iota_zeta env2 t1)
end
| uu____9889 -> begin
(norm cfg_exclude_iota_zeta env2 [] t1)
end))
in (

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____9909) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____9922 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____9960 uu____9961 -> (match (((uu____9960), (uu____9961))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____10015 = (norm_pat env3 p1)
in (match (uu____10015) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____9922) with
| (pats1, env3) -> begin
(((

let uu___206_10069 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___206_10069.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___207_10080 = x
in (

let uu____10081 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___207_10080.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___207_10080.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____10081}))
in (((

let uu___208_10087 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___208_10087.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___209_10091 = x
in (

let uu____10092 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___209_10091.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___209_10091.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____10092}))
in (((

let uu___210_10098 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___210_10098.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t1) -> begin
(

let x1 = (

let uu___211_10107 = x
in (

let uu____10108 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___211_10107.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___211_10107.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____10108}))
in (

let t2 = (norm_or_whnf env2 t1)
in (((

let uu___212_10115 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t2))); FStar_Syntax_Syntax.p = uu___212_10115.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let branches1 = (match (env1) with
| [] when whnf -> begin
branches
end
| uu____10118 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch1 -> (

let uu____10131 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____10131) with
| (p, wopt, e) -> begin
(

let uu____10147 = (norm_pat env1 p)
in (match (uu____10147) with
| (p1, env2) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____10168 = (norm_or_whnf env2 w)
in FStar_Pervasives_Native.Some (uu____10168))
end)
in (

let e1 = (norm_or_whnf env2 e)
in (FStar_Syntax_Util.branch ((p1), (wopt1), (e1)))))
end))
end)))))
end)
in (

let uu____10172 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches1)))) r)
in (rebuild cfg env1 stack2 uu____10172)))))));
))
in (

let rec is_cons = (fun head1 -> (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, uu____10182) -> begin
(is_cons h)
end
| FStar_Syntax_Syntax.Tm_constant (uu____10187) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10188; FStar_Syntax_Syntax.fv_delta = uu____10189; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10190; FStar_Syntax_Syntax.fv_delta = uu____10191; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____10192))}) -> begin
true
end
| uu____10196 -> begin
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

let uu____10292 = (FStar_Syntax_Util.head_and_args scrutinee1)
in (match (uu____10292) with
| (head1, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____10324) -> begin
FStar_Util.Inl ((scrutinee_orig)::[])
end
| FStar_Syntax_Syntax.Pat_wild (uu____10326) -> begin
FStar_Util.Inl ((scrutinee_orig)::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____10328) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| uu____10340 -> begin
(

let uu____10341 = (

let uu____10342 = (is_cons head1)
in (not (uu____10342)))
in FStar_Util.Inr (uu____10341))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let uu____10354 = (

let uu____10355 = (FStar_Syntax_Util.un_uinst head1)
in uu____10355.FStar_Syntax_Syntax.n)
in (match (uu____10354) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| uu____10362 -> begin
(

let uu____10363 = (

let uu____10364 = (is_cons head1)
in (not (uu____10364)))
in FStar_Util.Inr (uu____10363))
end))
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t1, uu____10395))::rest_a, ((p1, uu____10398))::rest_p) -> begin
(

let uu____10426 = (matches_pat t1 p1)
in (match (uu____10426) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____10440 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee1 p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p1, wopt, b))::rest -> begin
(

let uu____10511 = (matches_pat scrutinee1 p1)
in (match (uu____10511) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee1 rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
((log cfg (fun uu____10524 -> (

let uu____10525 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____10526 = (

let uu____10527 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right uu____10527 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" uu____10525 uu____10526)))));
(

let env2 = (FStar_List.fold_left (fun env2 t1 -> (

let uu____10539 = (

let uu____10540 = (

let uu____10550 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ((([]), (t1)))))
in (([]), (t1), (uu____10550), (false)))
in Clos (uu____10540))
in (uu____10539)::env2)) env1 s)
in (

let uu____10573 = (guard_when_clause wopt b rest)
in (norm cfg env2 stack2 uu____10573)));
)
end))
end))
in (

let uu____10574 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota))))
in (match (uu____10574) with
| true -> begin
(norm_and_rebuild_match ())
end
| uu____10575 -> begin
(matches scrutinee branches)
end))))))));
)
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun uu___149_10592 -> (match (uu___149_10592) with
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
| uu____10595 -> begin
[]
end))))
in (

let d1 = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| uu____10599 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d1; primitive_steps = built_in_primitive_steps})))


let normalize_with_primitive_steps : primitive_step Prims.list  ->  step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun ps s e t -> (

let c = (config s e)
in (

let c1 = (

let uu___213_10623 = (config s e)
in {steps = uu___213_10623.steps; tcenv = uu___213_10623.tcenv; delta_level = uu___213_10623.delta_level; primitive_steps = (FStar_List.append c.primitive_steps ps)})
in (norm c1 [] [] t))))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (normalize_with_primitive_steps [] s e t))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (

let uu____10648 = (config s e)
in (norm_comp uu____10648 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let uu____10657 = (config [] env)
in (norm_universe uu____10657 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (

let uu____10666 = (config [] env)
in (ghost_to_pure_aux uu____10666 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (

let uu____10680 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____10680)))
in (

let uu____10681 = ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ))
in (match (uu____10681) with
| true -> begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let uu___214_10683 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = uu___214_10683.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___214_10683.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____10686 -> (

let uu____10687 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env uu____10687)))})
end
| FStar_Pervasives_Native.None -> begin
lc
end)
end
| uu____10688 -> begin
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

let uu____10706 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_warning "Normalization failed with error %s" uu____10706));
t;
)
end
in (FStar_Syntax_Print.term_to_string t1)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let c1 = try
(match (()) with
| () -> begin
(

let uu____10719 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp uu____10719 [] c))
end)
with
| e -> begin
((

let uu____10726 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_warning "Normalization failed with error %s" uu____10726));
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

let uu____10766 = (

let uu____10767 = (

let uu____10772 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (uu____10772)))
in FStar_Syntax_Syntax.Tm_refine (uu____10767))
in (mk uu____10766 t01.FStar_Syntax_Syntax.pos))
end
| uu____10777 -> begin
t2
end))
end
| uu____10778 -> begin
t2
end)))
in (aux t))))


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((WHNF)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Beta)::[]) env t))


let reduce_or_remove_uvar_solutions : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun remove env t -> (normalize (FStar_List.append (match (remove) with
| true -> begin
(CheckNoUvars)::[]
end
| uu____10800 -> begin
[]
end) ((Beta)::(NoDeltaSteps)::(CompressUvars)::(Exclude (Zeta))::(Exclude (Iota))::(NoFullNorm)::[])) env t))


let reduce_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions false env t))


let remove_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions true env t))


let eta_expand_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e t_e -> (

let uu____10829 = (FStar_Syntax_Util.arrow_formals_comp t_e)
in (match (uu____10829) with
| (formals, c) -> begin
(match (formals) with
| [] -> begin
e
end
| uu____10845 -> begin
(

let uu____10849 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____10849) with
| (actuals, uu____10855, uu____10856) -> begin
(match (((FStar_List.length actuals) = (FStar_List.length formals))) with
| true -> begin
e
end
| uu____10871 -> begin
(

let uu____10872 = (FStar_All.pipe_right formals FStar_Syntax_Util.args_of_binders)
in (match (uu____10872) with
| (binders, args) -> begin
(

let uu____10882 = (FStar_Syntax_Syntax.mk_Tm_app e args FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Util.abs binders uu____10882 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c)))))
end))
end)
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____10893 = (

let uu____10897 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((uu____10897), (t.FStar_Syntax_Syntax.n)))
in (match (uu____10893) with
| (FStar_Pervasives_Native.Some (sort), uu____10904) -> begin
(

let uu____10906 = (mk sort t.FStar_Syntax_Syntax.pos)
in (eta_expand_with_type env t uu____10906))
end
| (uu____10907, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(eta_expand_with_type env t x.FStar_Syntax_Syntax.sort)
end
| uu____10911 -> begin
(

let uu____10915 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____10915) with
| (head1, args) -> begin
(

let uu____10941 = (

let uu____10942 = (FStar_Syntax_Subst.compress head1)
in uu____10942.FStar_Syntax_Syntax.n)
in (match (uu____10941) with
| FStar_Syntax_Syntax.Tm_uvar (uu____10945, thead) -> begin
(

let uu____10963 = (FStar_Syntax_Util.arrow_formals thead)
in (match (uu____10963) with
| (formals, tres) -> begin
(match (((FStar_List.length formals) = (FStar_List.length args))) with
| true -> begin
t
end
| uu____10997 -> begin
(

let uu____10998 = (env.FStar_TypeChecker_Env.type_of (

let uu___219_11003 = env
in {FStar_TypeChecker_Env.solver = uu___219_11003.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___219_11003.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___219_11003.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___219_11003.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___219_11003.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___219_11003.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___219_11003.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___219_11003.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___219_11003.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___219_11003.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___219_11003.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___219_11003.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___219_11003.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___219_11003.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___219_11003.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___219_11003.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___219_11003.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___219_11003.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___219_11003.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___219_11003.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___219_11003.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___219_11003.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___219_11003.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___219_11003.FStar_TypeChecker_Env.is_native_tactic}) t)
in (match (uu____10998) with
| (uu____11004, ty, uu____11006) -> begin
(eta_expand_with_type env t ty)
end))
end)
end))
end
| uu____11007 -> begin
(

let uu____11008 = (env.FStar_TypeChecker_Env.type_of (

let uu___220_11013 = env
in {FStar_TypeChecker_Env.solver = uu___220_11013.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___220_11013.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___220_11013.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___220_11013.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___220_11013.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___220_11013.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___220_11013.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___220_11013.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___220_11013.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___220_11013.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___220_11013.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___220_11013.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___220_11013.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___220_11013.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___220_11013.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___220_11013.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___220_11013.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___220_11013.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___220_11013.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___220_11013.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___220_11013.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___220_11013.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___220_11013.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___220_11013.FStar_TypeChecker_Env.is_native_tactic}) t)
in (match (uu____11008) with
| (uu____11014, ty, uu____11016) -> begin
(eta_expand_with_type env t ty)
end))
end))
end))
end)))


let elim_uvars_aux_tc : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.comp) FStar_Util.either  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * (FStar_Syntax_Syntax.term, (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax) FStar_Util.either) = (fun env univ_names binders tc -> (

let t = (match (((binders), (tc))) with
| ([], FStar_Util.Inl (t)) -> begin
t
end
| ([], FStar_Util.Inr (c)) -> begin
(failwith "Impossible: empty bindes with a comp")
end
| (uu____11066, FStar_Util.Inr (c)) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
end
| (uu____11074, FStar_Util.Inl (t)) -> begin
(

let uu____11078 = (

let uu____11081 = (

let uu____11082 = (

let uu____11090 = (FStar_Syntax_Syntax.mk_Total t)
in ((binders), (uu____11090)))
in FStar_Syntax_Syntax.Tm_arrow (uu____11082))
in (FStar_Syntax_Syntax.mk uu____11081))
in (uu____11078 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end)
in (

let uu____11099 = (FStar_Syntax_Subst.open_univ_vars univ_names t)
in (match (uu____11099) with
| (univ_names1, t1) -> begin
(

let t2 = (remove_uvar_solutions env t1)
in (

let t3 = (FStar_Syntax_Subst.close_univ_vars univ_names1 t2)
in (

let uu____11116 = (match (binders) with
| [] -> begin
(([]), (FStar_Util.Inl (t3)))
end
| uu____11148 -> begin
(

let uu____11149 = (

let uu____11154 = (

let uu____11155 = (FStar_Syntax_Subst.compress t3)
in uu____11155.FStar_Syntax_Syntax.n)
in ((uu____11154), (tc)))
in (match (uu____11149) with
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inr (uu____11171)) -> begin
((binders1), (FStar_Util.Inr (c)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inl (uu____11195)) -> begin
((binders1), (FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))))
end
| (uu____11221, FStar_Util.Inl (uu____11222)) -> begin
(([]), (FStar_Util.Inl (t3)))
end
| uu____11236 -> begin
(failwith "Impossible")
end))
end)
in (match (uu____11116) with
| (binders1, tc1) -> begin
((univ_names1), (binders1), (tc1))
end))))
end))))


let elim_uvars_aux_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term) = (fun env univ_names binders t -> (

let uu____11305 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl (t)))
in (match (uu____11305) with
| (univ_names1, binders1, tc) -> begin
(

let uu____11339 = (FStar_Util.left tc)
in ((univ_names1), (binders1), (uu____11339)))
end)))


let elim_uvars_aux_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax) = (fun env univ_names binders c -> (

let uu____11369 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr (c)))
in (match (uu____11369) with
| (univ_names1, binders1, tc) -> begin
(

let uu____11405 = (FStar_Util.right tc)
in ((univ_names1), (binders1), (uu____11405)))
end)))


let rec elim_uvars : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, lids, lids') -> begin
(

let uu____11433 = (elim_uvars_aux_t env univ_names binders typ)
in (match (uu____11433) with
| (univ_names1, binders1, typ1) -> begin
(

let uu___221_11449 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univ_names1), (binders1), (typ1), (lids), (lids'))); FStar_Syntax_Syntax.sigrng = uu___221_11449.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___221_11449.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___221_11449.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___221_11449.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uu___222_11461 = s
in (

let uu____11462 = (

let uu____11463 = (

let uu____11468 = (FStar_List.map (elim_uvars env) sigs)
in ((uu____11468), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____11463))
in {FStar_Syntax_Syntax.sigel = uu____11462; FStar_Syntax_Syntax.sigrng = uu___222_11461.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___222_11461.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___222_11461.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___222_11461.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univ_names, typ, lident, i, lids) -> begin
(

let uu____11480 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____11480) with
| (univ_names1, uu____11490, typ1) -> begin
(

let uu___223_11498 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univ_names1), (typ1), (lident), (i), (lids))); FStar_Syntax_Syntax.sigrng = uu___223_11498.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___223_11498.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___223_11498.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___223_11498.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) -> begin
(

let uu____11503 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____11503) with
| (univ_names1, uu____11513, typ1) -> begin
(

let uu___224_11521 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (univ_names1), (typ1))); FStar_Syntax_Syntax.sigrng = uu___224_11521.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___224_11521.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___224_11521.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___224_11521.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____11545 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____11545) with
| (opening, lbunivs) -> begin
(

let elim = (fun t -> (

let uu____11560 = (

let uu____11561 = (FStar_Syntax_Subst.subst opening t)
in (remove_uvar_solutions env uu____11561))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____11560)))
in (

let lbtyp = (elim lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (elim lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___225_11564 = lb
in {FStar_Syntax_Syntax.lbname = uu___225_11564.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___225_11564.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}))))
end)))))
in (

let uu___226_11565 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((b), (lbs1))), (lids))); FStar_Syntax_Syntax.sigrng = uu___226_11565.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___226_11565.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___226_11565.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___226_11565.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(

let uu___227_11572 = s
in (

let uu____11573 = (

let uu____11574 = (remove_uvar_solutions env t)
in FStar_Syntax_Syntax.Sig_main (uu____11574))
in {FStar_Syntax_Syntax.sigel = uu____11573; FStar_Syntax_Syntax.sigrng = uu___227_11572.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___227_11572.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___227_11572.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___227_11572.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, t) -> begin
(

let uu____11578 = (elim_uvars_aux_t env us [] t)
in (match (uu____11578) with
| (us1, uu____11588, t1) -> begin
(

let uu___228_11596 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((l), (us1), (t1))); FStar_Syntax_Syntax.sigrng = uu___228_11596.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___228_11596.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___228_11596.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___228_11596.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____11597) -> begin
(failwith "Impossible: should have been desugared already")
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____11599 = (elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____11599) with
| (univs1, binders, signature) -> begin
(

let uu____11615 = (

let uu____11620 = (FStar_Syntax_Subst.univ_var_opening univs1)
in (match (uu____11620) with
| (univs_opening, univs2) -> begin
(

let uu____11635 = (FStar_Syntax_Subst.univ_var_closing univs2)
in ((univs_opening), (uu____11635)))
end))
in (match (uu____11615) with
| (univs_opening, univs_closing) -> begin
(

let uu____11645 = (

let binders1 = (FStar_Syntax_Subst.open_binders binders)
in (

let uu____11649 = (FStar_Syntax_Subst.opening_of_binders binders1)
in (

let uu____11650 = (FStar_Syntax_Subst.closing_of_binders binders1)
in ((uu____11649), (uu____11650)))))
in (match (uu____11645) with
| (b_opening, b_closing) -> begin
(

let n1 = (FStar_List.length univs1)
in (

let n_binders = (FStar_List.length binders)
in (

let elim_tscheme = (fun uu____11669 -> (match (uu____11669) with
| (us, t) -> begin
(

let n_us = (FStar_List.length us)
in (

let uu____11682 = (FStar_Syntax_Subst.open_univ_vars us t)
in (match (uu____11682) with
| (us1, t1) -> begin
(

let uu____11689 = (

let uu____11692 = (FStar_All.pipe_right b_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____11699 = (FStar_All.pipe_right b_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____11692), (uu____11699))))
in (match (uu____11689) with
| (b_opening1, b_closing1) -> begin
(

let uu____11710 = (

let uu____11713 = (FStar_All.pipe_right univs_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____11721 = (FStar_All.pipe_right univs_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____11713), (uu____11721))))
in (match (uu____11710) with
| (univs_opening1, univs_closing1) -> begin
(

let t2 = (

let uu____11734 = (FStar_Syntax_Subst.subst b_opening1 t1)
in (FStar_Syntax_Subst.subst univs_opening1 uu____11734))
in (

let uu____11735 = (elim_uvars_aux_t env [] [] t2)
in (match (uu____11735) with
| (uu____11746, uu____11747, t3) -> begin
(

let t4 = (

let uu____11756 = (

let uu____11757 = (FStar_Syntax_Subst.close_univ_vars us1 t3)
in (FStar_Syntax_Subst.subst b_closing1 uu____11757))
in (FStar_Syntax_Subst.subst univs_closing1 uu____11756))
in ((us1), (t4)))
end)))
end))
end))
end)))
end))
in (

let elim_term = (fun t -> (

let uu____11762 = (elim_uvars_aux_t env univs1 binders t)
in (match (uu____11762) with
| (uu____11769, uu____11770, t1) -> begin
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
| uu____11817 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((a.FStar_Syntax_Syntax.action_params), (body), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
end))
in (

let destruct_action_body = (fun body -> (

let uu____11835 = (

let uu____11836 = (FStar_Syntax_Subst.compress body)
in uu____11836.FStar_Syntax_Syntax.n)
in (match (uu____11835) with
| FStar_Syntax_Syntax.Tm_ascribed (defn, (FStar_Util.Inl (typ), FStar_Pervasives_Native.None), FStar_Pervasives_Native.None) -> begin
((defn), (typ))
end
| uu____11884 -> begin
(failwith "Impossible")
end)))
in (

let destruct_action_typ_templ = (fun t -> (

let uu____11905 = (

let uu____11906 = (FStar_Syntax_Subst.compress t)
in uu____11906.FStar_Syntax_Syntax.n)
in (match (uu____11905) with
| FStar_Syntax_Syntax.Tm_abs (pars, body, uu____11921) -> begin
(

let uu____11934 = (destruct_action_body body)
in (match (uu____11934) with
| (defn, typ) -> begin
((pars), (defn), (typ))
end))
end
| uu____11968 -> begin
(

let uu____11969 = (destruct_action_body t)
in (match (uu____11969) with
| (defn, typ) -> begin
(([]), (defn), (typ))
end))
end)))
in (

let uu____12005 = (elim_tscheme ((a.FStar_Syntax_Syntax.action_univs), (action_typ_templ)))
in (match (uu____12005) with
| (action_univs, t) -> begin
(

let uu____12012 = (destruct_action_typ_templ t)
in (match (uu____12012) with
| (action_params, action_defn, action_typ) -> begin
(

let a' = (

let uu___229_12041 = a
in {FStar_Syntax_Syntax.action_name = uu___229_12041.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___229_12041.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action_univs; FStar_Syntax_Syntax.action_params = action_params; FStar_Syntax_Syntax.action_defn = action_defn; FStar_Syntax_Syntax.action_typ = action_typ})
in a')
end))
end))))))
in (

let ed1 = (

let uu___230_12043 = ed
in (

let uu____12044 = (elim_tscheme ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____12045 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____12046 = (elim_tscheme ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____12047 = (elim_tscheme ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____12048 = (elim_tscheme ed.FStar_Syntax_Syntax.stronger)
in (

let uu____12049 = (elim_tscheme ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____12050 = (elim_tscheme ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____12051 = (elim_tscheme ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____12052 = (elim_tscheme ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____12053 = (elim_tscheme ed.FStar_Syntax_Syntax.trivial)
in (

let uu____12054 = (elim_term ed.FStar_Syntax_Syntax.repr)
in (

let uu____12055 = (elim_tscheme ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____12056 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____12057 = (FStar_List.map elim_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___230_12043.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___230_12043.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu____12044; FStar_Syntax_Syntax.bind_wp = uu____12045; FStar_Syntax_Syntax.if_then_else = uu____12046; FStar_Syntax_Syntax.ite_wp = uu____12047; FStar_Syntax_Syntax.stronger = uu____12048; FStar_Syntax_Syntax.close_wp = uu____12049; FStar_Syntax_Syntax.assert_p = uu____12050; FStar_Syntax_Syntax.assume_p = uu____12051; FStar_Syntax_Syntax.null_wp = uu____12052; FStar_Syntax_Syntax.trivial = uu____12053; FStar_Syntax_Syntax.repr = uu____12054; FStar_Syntax_Syntax.return_repr = uu____12055; FStar_Syntax_Syntax.bind_repr = uu____12056; FStar_Syntax_Syntax.actions = uu____12057})))))))))))))))
in (

let uu___231_12059 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ed1); FStar_Syntax_Syntax.sigrng = uu___231_12059.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___231_12059.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___231_12059.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___231_12059.FStar_Syntax_Syntax.sigattrs})))))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub_eff) -> begin
(

let elim_tscheme_opt = (fun uu___150_12070 -> (match (uu___150_12070) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (us, t) -> begin
(

let uu____12085 = (elim_uvars_aux_t env us [] t)
in (match (uu____12085) with
| (us1, uu____12098, t1) -> begin
FStar_Pervasives_Native.Some (((us1), (t1)))
end))
end))
in (

let sub_eff1 = (

let uu___232_12109 = sub_eff
in (

let uu____12110 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp)
in (

let uu____12112 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift)
in {FStar_Syntax_Syntax.source = uu___232_12109.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___232_12109.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = uu____12110; FStar_Syntax_Syntax.lift = uu____12112})))
in (

let uu___233_12114 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub_eff1); FStar_Syntax_Syntax.sigrng = uu___233_12114.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___233_12114.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___233_12114.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___233_12114.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univ_names, binders, comp, flags) -> begin
(

let uu____12122 = (elim_uvars_aux_c env univ_names binders comp)
in (match (uu____12122) with
| (univ_names1, binders1, comp1) -> begin
(

let uu___234_12144 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (univ_names1), (binders1), (comp1), (flags))); FStar_Syntax_Syntax.sigrng = uu___234_12144.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___234_12144.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___234_12144.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___234_12144.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_pragma (uu____12151) -> begin
s
end))




