
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
| PureSubtermsWithinComputations
| Simplify
| EraseUniverses
| AllowUnboundUniverses
| Reify
| CompressUvars
| NoFullNorm


let uu___is_Beta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Beta -> begin
true
end
| uu____12 -> begin
false
end))


let uu___is_Iota : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iota -> begin
true
end
| uu____16 -> begin
false
end))


let uu___is_Zeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Zeta -> begin
true
end
| uu____20 -> begin
false
end))


let uu___is_Exclude : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
true
end
| uu____25 -> begin
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
| uu____36 -> begin
false
end))


let uu___is_Primops : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____40 -> begin
false
end))


let uu___is_Eager_unfolding : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding -> begin
true
end
| uu____44 -> begin
false
end))


let uu___is_Inlining : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____48 -> begin
false
end))


let uu___is_NoDeltaSteps : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoDeltaSteps -> begin
true
end
| uu____52 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____57 -> begin
false
end))


let __proj__UnfoldUntil__item___0 : step  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
_0
end))


let uu___is_PureSubtermsWithinComputations : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PureSubtermsWithinComputations -> begin
true
end
| uu____68 -> begin
false
end))


let uu___is_Simplify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simplify -> begin
true
end
| uu____72 -> begin
false
end))


let uu___is_EraseUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EraseUniverses -> begin
true
end
| uu____76 -> begin
false
end))


let uu___is_AllowUnboundUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AllowUnboundUniverses -> begin
true
end
| uu____80 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____84 -> begin
false
end))


let uu___is_CompressUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CompressUvars -> begin
true
end
| uu____88 -> begin
false
end))


let uu___is_NoFullNorm : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoFullNorm -> begin
true
end
| uu____92 -> begin
false
end))


type steps =
step Prims.list

type primitive_step =
{name : FStar_Ident.lid; arity : Prims.int; strong_reduction_ok : Prims.bool; interpretation : FStar_Range.range  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option}

type closure =
| Clos of (closure Prims.list * FStar_Syntax_Syntax.term * (closure Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
| Univ of FStar_Syntax_Syntax.universe
| Dummy


let uu___is_Clos : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Clos (_0) -> begin
true
end
| uu____175 -> begin
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
| uu____214 -> begin
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
| uu____225 -> begin
false
end))


type env =
closure Prims.list


let closure_to_string : closure  ->  Prims.string = (fun uu___130_229 -> (match (uu___130_229) with
| Clos (uu____230, t, uu____232, uu____233) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| Univ (uu____244) -> begin
"Univ"
end
| Dummy -> begin
"dummy"
end))

type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level Prims.list; primitive_steps : primitive_step Prims.list}


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list


type subst_t =
FStar_Syntax_Syntax.subst_elt Prims.list

type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either FStar_Pervasives_Native.option * FStar_Range.range)
| App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range)
| Let of (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range)
| Steps of (steps * primitive_step Prims.list * FStar_TypeChecker_Env.delta_level Prims.list)
| Debug of FStar_Syntax_Syntax.term


let uu___is_Arg : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Arg (_0) -> begin
true
end
| uu____371 -> begin
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
| uu____395 -> begin
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
| uu____419 -> begin
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
| uu____446 -> begin
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
| uu____475 -> begin
false
end))


let __proj__Abs__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * env * (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either FStar_Pervasives_Native.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Abs (_0) -> begin
_0
end))


let uu___is_App : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| App (_0) -> begin
true
end
| uu____514 -> begin
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
| uu____537 -> begin
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
| uu____559 -> begin
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
| uu____588 -> begin
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
| uu____615 -> begin
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

let uu____663 = (FStar_ST.read r)
in (match (uu____663) with
| FStar_Pervasives_Native.Some (uu____668) -> begin
(failwith "Unexpected set_memo: thunk already evaluated")
end
| FStar_Pervasives_Native.None -> begin
(FStar_ST.write r (FStar_Pervasives_Native.Some (t)))
end)))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (

let uu____677 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right uu____677 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun uu___131_682 -> (match (uu___131_682) with
| Arg (c, uu____684, uu____685) -> begin
(

let uu____686 = (closure_to_string c)
in (FStar_Util.format1 "Closure %s" uu____686))
end
| MemoLazy (uu____687) -> begin
"MemoLazy"
end
| Abs (uu____691, bs, uu____693, uu____694, uu____695) -> begin
(

let uu____702 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" uu____702))
end
| UnivArgs (uu____707) -> begin
"UnivArgs"
end
| Match (uu____711) -> begin
"Match"
end
| App (t, uu____716, uu____717) -> begin
(

let uu____718 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "App %s" uu____718))
end
| Meta (m, uu____720) -> begin
"Meta"
end
| Let (uu____721) -> begin
"Let"
end
| Steps (uu____726, uu____727, uu____728) -> begin
"Steps"
end
| Debug (t) -> begin
(

let uu____734 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Debug %s" uu____734))
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (

let uu____740 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right uu____740 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> (

let uu____754 = (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm")))
in (match (uu____754) with
| true -> begin
(f ())
end
| uu____755 -> begin
()
end)))


let is_empty = (fun uu___132_763 -> (match (uu___132_763) with
| [] -> begin
true
end
| uu____765 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| uu____783 -> begin
(

let uu____784 = (

let uu____785 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" uu____785))
in (failwith uu____784))
end)


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun l -> (match ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Pure_lid)
end
| uu____791 -> begin
(match ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Tot_lid)
end
| uu____793 -> begin
(match ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_PURE_lid)
end
| uu____795 -> begin
FStar_Pervasives_Native.None
end)
end)
end))


let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us1 = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let uu____816 = (FStar_List.fold_left (fun uu____825 u1 -> (match (uu____825) with
| (cur_kernel, cur_max, out) -> begin
(

let uu____840 = (FStar_Syntax_Util.univ_kernel u1)
in (match (uu____840) with
| (k_u, n1) -> begin
(

let uu____849 = (FStar_Syntax_Util.eq_univs cur_kernel k_u)
in (match (uu____849) with
| true -> begin
((cur_kernel), (u1), (out))
end
| uu____855 -> begin
((k_u), (u1), ((cur_max)::out))
end))
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us1)
in (match (uu____816) with
| (uu____859, u1, out) -> begin
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

let uu____875 = (FStar_List.nth env x)
in (match (uu____875) with
| Univ (u3) -> begin
(aux u3)
end
| Dummy -> begin
(u2)::[]
end
| uu____878 -> begin
(failwith "Impossible: universe variable bound to a term")
end))
end)
with
| uu____882 -> begin
(

let uu____883 = (FStar_All.pipe_right cfg.steps (FStar_List.contains AllowUnboundUniverses))
in (match (uu____883) with
| true -> begin
(FStar_Syntax_Syntax.U_unknown)::[]
end
| uu____885 -> begin
(failwith "Universe variable not found")
end))
end
end
| FStar_Syntax_Syntax.U_zero -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_unif (uu____887) -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_name (uu____890) -> begin
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

let uu____895 = (FStar_List.collect aux us)
in (FStar_All.pipe_right uu____895 norm_univs))
in (match (us1) with
| (u_k)::(hd1)::rest -> begin
(

let rest1 = (hd1)::rest
in (

let uu____906 = (FStar_Syntax_Util.univ_kernel u_k)
in (match (uu____906) with
| (FStar_Syntax_Syntax.U_zero, n1) -> begin
(

let uu____911 = (FStar_All.pipe_right rest1 (FStar_List.for_all (fun u3 -> (

let uu____914 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____914) with
| (uu____917, m) -> begin
(n1 <= m)
end)))))
in (match (uu____911) with
| true -> begin
rest1
end
| uu____920 -> begin
us1
end))
end
| uu____921 -> begin
us1
end)))
end
| uu____924 -> begin
us1
end))
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____927 = (aux u3)
in (FStar_List.map (fun _0_30 -> FStar_Syntax_Syntax.U_succ (_0_30)) uu____927))
end)))
in (

let uu____929 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____929) with
| true -> begin
FStar_Syntax_Syntax.U_unknown
end
| uu____930 -> begin
(

let uu____931 = (aux u)
in (match (uu____931) with
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


let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> ((log cfg (fun uu____1028 -> (

let uu____1029 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1030 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1029 uu____1030)))));
(match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| uu____1031 -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1034) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t1
end
| FStar_Syntax_Syntax.Tm_constant (uu____1055) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_name (uu____1056) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1057) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1058) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____1068 = (

let uu____1069 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (uu____1069))
in (mk uu____1068 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t2, us) -> begin
(

let uu____1076 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t2 uu____1076))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____1078 = (lookup_bvar env x)
in (match (uu____1078) with
| Univ (uu____1079) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t1
end
| Clos (env1, t0, r, uu____1083) -> begin
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

let uu____1151 = (closures_as_binders_delayed cfg env bs)
in (match (uu____1151) with
| (bs1, env1) -> begin
(

let body1 = (closure_as_term_delayed cfg env1 body)
in (

let uu____1171 = (

let uu____1172 = (

let uu____1187 = (close_lcomp_opt cfg env1 lopt)
in ((bs1), (body1), (uu____1187)))
in FStar_Syntax_Syntax.Tm_abs (uu____1172))
in (mk uu____1171 t1.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1217 = (closures_as_binders_delayed cfg env bs)
in (match (uu____1217) with
| (bs1, env1) -> begin
(

let c1 = (close_comp cfg env1 c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs1), (c1)))) t1.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____1248 = (

let uu____1255 = (

let uu____1259 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1259)::[])
in (closures_as_binders_delayed cfg env uu____1255))
in (match (uu____1248) with
| (x1, env1) -> begin
(

let phi1 = (closure_as_term_delayed cfg env1 phi)
in (

let uu____1273 = (

let uu____1274 = (

let uu____1279 = (

let uu____1280 = (FStar_List.hd x1)
in (FStar_All.pipe_right uu____1280 FStar_Pervasives_Native.fst))
in ((uu____1279), (phi1)))
in FStar_Syntax_Syntax.Tm_refine (uu____1274))
in (mk uu____1273 t1.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (annot, tacopt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____1348 = (closure_as_term_delayed cfg env t2)
in FStar_Util.Inl (uu____1348))
end
| FStar_Util.Inr (c) -> begin
(

let uu____1362 = (close_comp cfg env c)
in FStar_Util.Inr (uu____1362))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (closure_as_term_delayed cfg env))
in (

let uu____1377 = (

let uu____1378 = (

let uu____1396 = (closure_as_term_delayed cfg env t11)
in ((uu____1396), (((annot1), (tacopt1))), (lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____1378))
in (mk uu____1377 t1.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____1434 = (

let uu____1435 = (

let uu____1440 = (closure_as_term_delayed cfg env t')
in (

let uu____1443 = (

let uu____1444 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (uu____1444))
in ((uu____1440), (uu____1443))))
in FStar_Syntax_Syntax.Tm_meta (uu____1435))
in (mk uu____1434 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(

let uu____1486 = (

let uu____1487 = (

let uu____1492 = (closure_as_term_delayed cfg env t')
in (

let uu____1495 = (

let uu____1496 = (

let uu____1501 = (closure_as_term_delayed cfg env tbody)
in ((m), (uu____1501)))
in FStar_Syntax_Syntax.Meta_monadic (uu____1496))
in ((uu____1492), (uu____1495))))
in FStar_Syntax_Syntax.Tm_meta (uu____1487))
in (mk uu____1486 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody)) -> begin
(

let uu____1520 = (

let uu____1521 = (

let uu____1526 = (closure_as_term_delayed cfg env t')
in (

let uu____1529 = (

let uu____1530 = (

let uu____1536 = (closure_as_term_delayed cfg env tbody)
in ((m1), (m2), (uu____1536)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____1530))
in ((uu____1526), (uu____1529))))
in FStar_Syntax_Syntax.Tm_meta (uu____1521))
in (mk uu____1520 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(

let uu____1549 = (

let uu____1550 = (

let uu____1555 = (closure_as_term_delayed cfg env t')
in ((uu____1555), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____1550))
in (mk uu____1549 t1.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env1 = (FStar_List.fold_left (fun env1 uu____1576 -> (Dummy)::env1) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef)
in (

let body1 = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____1587) -> begin
body
end
| FStar_Util.Inl (uu____1588) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb1 = (

let uu___145_1590 = lb
in {FStar_Syntax_Syntax.lbname = uu___145_1590.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___145_1590.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = uu___145_1590.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (body1)))) t1.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((uu____1597, lbs), body) -> begin
(

let norm_one_lb = (fun env1 lb -> (

let env_univs = (FStar_List.fold_right (fun uu____1621 env2 -> (Dummy)::env2) lb.FStar_Syntax_Syntax.lbunivs env1)
in (

let env2 = (

let uu____1626 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____1626) with
| true -> begin
env_univs
end
| uu____1628 -> begin
(FStar_List.fold_right (fun uu____1630 env2 -> (Dummy)::env2) lbs env_univs)
end))
in (

let uu___146_1633 = lb
in (

let uu____1634 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____1637 = (closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___146_1633.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___146_1633.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____1634; FStar_Syntax_Syntax.lbeff = uu___146_1633.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____1637}))))))
in (

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body1 = (

let body_env = (FStar_List.fold_right (fun uu____1648 env1 -> (Dummy)::env1) lbs1 env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs1))), (body1)))) t1.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let head2 = (closure_as_term cfg env head1)
in (

let norm_one_branch = (fun env1 uu____1703 -> (match (uu____1703) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____1749) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1765 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1799 uu____1800 -> (match (((uu____1799), (uu____1800))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____1865 = (norm_pat env3 p1)
in (match (uu____1865) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____1765) with
| (pats1, env3) -> begin
(((

let uu___147_1931 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.ty = uu___147_1931.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___147_1931.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___148_1945 = x
in (

let uu____1946 = (closure_as_term cfg env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___148_1945.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___148_1945.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1946}))
in (((

let uu___149_1952 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.ty = uu___149_1952.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___149_1952.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___150_1957 = x
in (

let uu____1958 = (closure_as_term cfg env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___150_1957.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_1957.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1958}))
in (((

let uu___151_1964 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.ty = uu___151_1964.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___151_1964.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t2) -> begin
(

let x1 = (

let uu___152_1974 = x
in (

let uu____1975 = (closure_as_term cfg env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___152_1974.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___152_1974.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1975}))
in (

let t3 = (closure_as_term cfg env2 t2)
in (((

let uu___153_1982 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t3))); FStar_Syntax_Syntax.ty = uu___153_1982.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___153_1982.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let uu____1985 = (norm_pat env1 pat)
in (match (uu____1985) with
| (pat1, env2) -> begin
(

let w_opt1 = (match (w_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____2009 = (closure_as_term cfg env2 w)
in FStar_Pervasives_Native.Some (uu____2009))
end)
in (

let tm1 = (closure_as_term cfg env2 tm)
in ((pat1), (w_opt1), (tm1))))
end)))
end))
in (

let uu____2014 = (

let uu____2015 = (

let uu____2031 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head2), (uu____2031)))
in FStar_Syntax_Syntax.Tm_match (uu____2015))
in (mk uu____2014 t1.FStar_Syntax_Syntax.pos))))
end))
end);
))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| uu____2084 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| uu____2100 -> begin
(FStar_List.map (fun uu____2110 -> (match (uu____2110) with
| (x, imp) -> begin
(

let uu____2125 = (closure_as_term_delayed cfg env x)
in ((uu____2125), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * closure Prims.list) = (fun cfg env bs -> (

let uu____2137 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2161 uu____2162 -> (match (((uu____2161), (uu____2162))) with
| ((env1, out), (b, imp)) -> begin
(

let b1 = (

let uu___154_2206 = b
in (

let uu____2207 = (closure_as_term_delayed cfg env1 b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___154_2206.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___154_2206.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2207}))
in (

let env2 = (Dummy)::env1
in ((env2), ((((b1), (imp)))::out))))
end)) ((env), ([]))))
in (match (uu____2137) with
| (env1, bs1) -> begin
(((FStar_List.rev bs1)), (env1))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| uu____2254 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____2266 = (closure_as_term_delayed cfg env t)
in (

let uu____2267 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____2266 uu____2267)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____2277 = (closure_as_term_delayed cfg env t)
in (

let uu____2278 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____2277 uu____2278)))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let rt = (closure_as_term_delayed cfg env c1.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c1.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___133_2294 -> (match (uu___133_2294) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____2298 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (uu____2298))
end
| f -> begin
f
end))))
in (

let uu____2302 = (

let uu___155_2303 = c1
in (

let uu____2304 = (FStar_List.map (norm_universe cfg env) c1.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = uu____2304; FStar_Syntax_Syntax.effect_name = uu___155_2303.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp uu____2302)))))
end)
end))
and filter_out_lcomp_cflags : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun lc -> (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.filter (fun uu___134_2308 -> (match (uu___134_2308) with
| FStar_Syntax_Syntax.DECREASES (uu____2309) -> begin
false
end
| uu____2312 -> begin
true
end)))))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) -> begin
(

let flags = (filter_out_lcomp_cflags lc)
in (

let uu____2340 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____2340) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Util.Inr (((FStar_Parser_Const.effect_Tot_lid), (flags))))
end
| uu____2356 -> begin
(

let uu____2357 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____2357) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Util.Inr (((FStar_Parser_Const.effect_GTot_lid), (flags))))
end
| uu____2373 -> begin
FStar_Pervasives_Native.Some (FStar_Util.Inr (((lc.FStar_Syntax_Syntax.eff_name), (flags))))
end))
end)))
end
| uu____2383 -> begin
lopt
end))


let built_in_primitive_steps : primitive_step Prims.list = (

let const_as_tm = (fun c p -> (mk (FStar_Syntax_Syntax.Tm_constant (c)) p))
in (

let int_as_const = (fun p i -> (

let uu____2407 = (

let uu____2408 = (

let uu____2414 = (FStar_Util.string_of_int i)
in ((uu____2414), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____2408))
in (const_as_tm uu____2407 p)))
in (

let bool_as_const = (fun p b -> (const_as_tm (FStar_Const.Const_bool (b)) p))
in (

let string_as_const = (fun p b -> (const_as_tm (FStar_Const.Const_string (((b), (p)))) p))
in (

let arg_as_int = (fun uu____2440 -> (match (uu____2440) with
| (a, uu____2445) -> begin
(

let uu____2447 = (

let uu____2448 = (FStar_Syntax_Subst.compress a)
in uu____2448.FStar_Syntax_Syntax.n)
in (match (uu____2447) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, FStar_Pervasives_Native.None)) -> begin
(

let uu____2458 = (FStar_Util.int_of_string i)
in FStar_Pervasives_Native.Some (uu____2458))
end
| uu____2459 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_bounded_int = (fun uu____2468 -> (match (uu____2468) with
| (a, uu____2475) -> begin
(

let uu____2479 = (

let uu____2480 = (FStar_Syntax_Subst.compress a)
in uu____2480.FStar_Syntax_Syntax.n)
in (match (uu____2479) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv1); FStar_Syntax_Syntax.tk = uu____2487; FStar_Syntax_Syntax.pos = uu____2488; FStar_Syntax_Syntax.vars = uu____2489}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, FStar_Pervasives_Native.None)); FStar_Syntax_Syntax.tk = uu____2491; FStar_Syntax_Syntax.pos = uu____2492; FStar_Syntax_Syntax.vars = uu____2493}, uu____2494))::[]) when (FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") -> begin
(

let uu____2525 = (

let uu____2528 = (FStar_Util.int_of_string i)
in ((fv1), (uu____2528)))
in FStar_Pervasives_Native.Some (uu____2525))
end
| uu____2531 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_bool = (fun uu____2540 -> (match (uu____2540) with
| (a, uu____2545) -> begin
(

let uu____2547 = (

let uu____2548 = (FStar_Syntax_Subst.compress a)
in uu____2548.FStar_Syntax_Syntax.n)
in (match (uu____2547) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (b)) -> begin
FStar_Pervasives_Native.Some (b)
end
| uu____2553 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_char = (fun uu____2560 -> (match (uu____2560) with
| (a, uu____2565) -> begin
(

let uu____2567 = (

let uu____2568 = (FStar_Syntax_Subst.compress a)
in uu____2568.FStar_Syntax_Syntax.n)
in (match (uu____2567) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c)) -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____2573 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_string = (fun uu____2580 -> (match (uu____2580) with
| (a, uu____2585) -> begin
(

let uu____2587 = (

let uu____2588 = (FStar_Syntax_Subst.compress a)
in uu____2588.FStar_Syntax_Syntax.n)
in (match (uu____2587) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____2593)) -> begin
FStar_Pervasives_Native.Some (s)
end
| uu____2594 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_list = (fun f uu____2615 -> (match (uu____2615) with
| (a, uu____2624) -> begin
(

let rec sequence = (fun l -> (match (l) with
| [] -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Pervasives_Native.None)::uu____2643 -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.Some (x))::xs -> begin
(

let uu____2653 = (sequence xs)
in (match (uu____2653) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (xs') -> begin
FStar_Pervasives_Native.Some ((x)::xs')
end))
end))
in (

let uu____2664 = (FStar_Syntax_Util.list_elements a)
in (match (uu____2664) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (elts) -> begin
(

let uu____2674 = (FStar_List.map (fun x -> (

let uu____2679 = (FStar_Syntax_Syntax.as_arg x)
in (f uu____2679))) elts)
in (sequence uu____2674))
end)))
end))
in (

let lift_unary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a))::[] -> begin
(

let uu____2709 = (f a)
in FStar_Pervasives_Native.Some (uu____2709))
end
| uu____2710 -> begin
FStar_Pervasives_Native.None
end))
in (

let lift_binary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a0))::(FStar_Pervasives_Native.Some (a1))::[] -> begin
(

let uu____2749 = (f a0 a1)
in FStar_Pervasives_Native.Some (uu____2749))
end
| uu____2750 -> begin
FStar_Pervasives_Native.None
end))
in (

let unary_op = (fun as_a f r args -> (

let uu____2794 = (FStar_List.map as_a args)
in (lift_unary (f r) uu____2794)))
in (

let binary_op = (fun as_a f r args -> (

let uu____2844 = (FStar_List.map as_a args)
in (lift_binary (f r) uu____2844)))
in (

let as_primitive_step = (fun uu____2861 -> (match (uu____2861) with
| (l, arity, f) -> begin
{name = l; arity = arity; strong_reduction_ok = true; interpretation = f}
end))
in (

let unary_int_op = (fun f -> (unary_op arg_as_int (fun r x -> (

let uu____2899 = (f x)
in (int_as_const r uu____2899)))))
in (

let binary_int_op = (fun f -> (binary_op arg_as_int (fun r x y -> (

let uu____2922 = (f x y)
in (int_as_const r uu____2922)))))
in (

let unary_bool_op = (fun f -> (unary_op arg_as_bool (fun r x -> (

let uu____2939 = (f x)
in (bool_as_const r uu____2939)))))
in (

let binary_bool_op = (fun f -> (binary_op arg_as_bool (fun r x y -> (

let uu____2962 = (f x y)
in (bool_as_const r uu____2962)))))
in (

let binary_string_op = (fun f -> (binary_op arg_as_string (fun r x y -> (

let uu____2985 = (f x y)
in (string_as_const r uu____2985)))))
in (

let list_of_string' = (fun rng s -> (

let name = (fun l -> (

let uu____2999 = (

let uu____3000 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____3000))
in (mk uu____2999 rng)))
in (

let char_t = (name FStar_Parser_Const.char_lid)
in (

let charterm = (fun c -> (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))) rng))
in (

let uu____3010 = (

let uu____3012 = (FStar_String.list_of_string s)
in (FStar_List.map charterm uu____3012))
in (FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3010))))))
in (

let string_of_list' = (fun rng l -> (

let s = (FStar_String.string_of_list l)
in (FStar_Syntax_Util.exp_string s)))
in (

let string_of_int1 = (fun rng i -> (

let uu____3034 = (FStar_Util.string_of_int i)
in (string_as_const rng uu____3034)))
in (

let string_of_bool1 = (fun rng b -> (string_as_const rng (match (b) with
| true -> begin
"true"
end
| uu____3042 -> begin
"false"
end)))
in (

let string_of_int2 = (fun rng i -> (

let uu____3050 = (FStar_Util.string_of_int i)
in (string_as_const rng uu____3050)))
in (

let string_of_bool2 = (fun rng b -> (string_as_const rng (match (b) with
| true -> begin
"true"
end
| uu____3058 -> begin
"false"
end)))
in (

let basic_ops = (

let uu____3069 = (

let uu____3079 = (

let uu____3089 = (

let uu____3099 = (

let uu____3109 = (

let uu____3119 = (

let uu____3129 = (

let uu____3139 = (

let uu____3149 = (

let uu____3159 = (

let uu____3169 = (

let uu____3179 = (

let uu____3189 = (

let uu____3199 = (

let uu____3209 = (

let uu____3219 = (

let uu____3229 = (

let uu____3238 = (FStar_Parser_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((uu____3238), ((Prims.parse_int "1")), ((unary_op arg_as_string list_of_string'))))
in (

let uu____3244 = (

let uu____3254 = (

let uu____3263 = (FStar_Parser_Const.p2l (("FStar")::("String")::("string_of_list")::[]))
in ((uu____3263), ((Prims.parse_int "1")), ((unary_op (arg_as_list arg_as_char) string_of_list'))))
in (uu____3254)::[])
in (uu____3229)::uu____3244))
in (((FStar_Parser_Const.string_of_bool_lid), ((Prims.parse_int "1")), ((unary_op arg_as_bool string_of_bool2))))::uu____3219)
in (((FStar_Parser_Const.string_of_int_lid), ((Prims.parse_int "1")), ((unary_op arg_as_int string_of_int2))))::uu____3209)
in (((FStar_Parser_Const.strcat_lid), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____3199)
in (((FStar_Parser_Const.op_Or), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x || y))))))::uu____3189)
in (((FStar_Parser_Const.op_And), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x && y))))))::uu____3179)
in (((FStar_Parser_Const.op_Negation), ((Prims.parse_int "1")), ((unary_bool_op (fun x -> (not (x)))))))::uu____3169)
in (((FStar_Parser_Const.op_Modulus), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x mod y))))))::uu____3159)
in (((FStar_Parser_Const.op_GTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x >= y)))))))::uu____3149)
in (((FStar_Parser_Const.op_GT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x > y)))))))::uu____3139)
in (((FStar_Parser_Const.op_LTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x <= y)))))))::uu____3129)
in (((FStar_Parser_Const.op_LT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x < y)))))))::uu____3119)
in (((FStar_Parser_Const.op_Division), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x / y))))))::uu____3109)
in (((FStar_Parser_Const.op_Multiply), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x * y))))))::uu____3099)
in (((FStar_Parser_Const.op_Subtraction), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x - y))))))::uu____3089)
in (((FStar_Parser_Const.op_Addition), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x + y))))))::uu____3079)
in (((FStar_Parser_Const.op_Minus), ((Prims.parse_int "1")), ((unary_int_op (fun x -> (~- (x)))))))::uu____3069)
in (

let bounded_arith_ops = (

let bounded_int_types = ("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]
in (

let int_as_bounded = (fun r int_to_t1 n1 -> (

let c = (int_as_const r n1)
in (

let int_to_t2 = (FStar_Syntax_Syntax.fv_to_tm int_to_t1)
in (

let uu____3558 = (

let uu____3559 = (

let uu____3560 = (FStar_Syntax_Syntax.as_arg c)
in (uu____3560)::[])
in (FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3559))
in (uu____3558 FStar_Pervasives_Native.None r)))))
in (FStar_All.pipe_right bounded_int_types (FStar_List.collect (fun m -> (

let uu____3584 = (

let uu____3593 = (FStar_Parser_Const.p2l (("FStar")::(m)::("add")::[]))
in ((uu____3593), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____3602 uu____3603 -> (match (((uu____3602), (uu____3603))) with
| ((int_to_t1, x), (uu____3614, y)) -> begin
(int_as_bounded r int_to_t1 (x + y))
end))))))
in (

let uu____3620 = (

let uu____3630 = (

let uu____3639 = (FStar_Parser_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((uu____3639), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____3648 uu____3649 -> (match (((uu____3648), (uu____3649))) with
| ((int_to_t1, x), (uu____3660, y)) -> begin
(int_as_bounded r int_to_t1 (x - y))
end))))))
in (

let uu____3666 = (

let uu____3676 = (

let uu____3685 = (FStar_Parser_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((uu____3685), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____3694 uu____3695 -> (match (((uu____3694), (uu____3695))) with
| ((int_to_t1, x), (uu____3706, y)) -> begin
(int_as_bounded r int_to_t1 (x * y))
end))))))
in (uu____3676)::[])
in (uu____3630)::uu____3666))
in (uu____3584)::uu____3620)))))))
in (FStar_List.map as_primitive_step (FStar_List.append basic_ops bounded_arith_ops))))))))))))))))))))))))))))))


let equality_ops : primitive_step Prims.list = (

let interp_bool = (fun rng args -> (match (args) with
| ((_typ, uu____3772))::((a1, uu____3774))::((a2, uu____3776))::[] -> begin
(

let uu____3805 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____3805) with
| FStar_Syntax_Util.Equal -> begin
(

let uu____3807 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) rng)
in FStar_Pervasives_Native.Some (uu____3807))
end
| FStar_Syntax_Util.NotEqual -> begin
(

let uu____3812 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) rng)
in FStar_Pervasives_Native.Some (uu____3812))
end
| uu____3817 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____3818 -> begin
(failwith "Unexpected number of arguments")
end))
in (

let interp_prop = (fun r args -> (match (args) with
| ((_typ, uu____3831))::((a1, uu____3833))::((a2, uu____3835))::[] -> begin
(

let uu____3864 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____3864) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___156_3868 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___156_3868.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___156_3868.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___156_3868.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___157_3875 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___157_3875.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___157_3875.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___157_3875.FStar_Syntax_Syntax.vars}))
end
| uu____3880 -> begin
FStar_Pervasives_Native.None
end))
end
| ((_typ, uu____3882))::(uu____3883)::((a1, uu____3885))::((a2, uu____3887))::[] -> begin
(

let uu____3924 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____3924) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___156_3928 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___156_3928.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___156_3928.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___156_3928.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___157_3935 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___157_3935.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___157_3935.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___157_3935.FStar_Syntax_Syntax.vars}))
end
| uu____3940 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____3941 -> begin
(failwith "Unexpected number of arguments")
end))
in (

let decidable_equality = {name = FStar_Parser_Const.op_Eq; arity = (Prims.parse_int "3"); strong_reduction_ok = true; interpretation = interp_bool}
in (

let propositional_equality = {name = FStar_Parser_Const.eq2_lid; arity = (Prims.parse_int "3"); strong_reduction_ok = true; interpretation = interp_prop}
in (

let hetero_propositional_equality = {name = FStar_Parser_Const.eq3_lid; arity = (Prims.parse_int "4"); strong_reduction_ok = true; interpretation = interp_prop}
in (decidable_equality)::(propositional_equality)::(hetero_propositional_equality)::[])))))


let reduce_primops : cfg  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (

let uu____3952 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops cfg.steps))
in (match (uu____3952) with
| true -> begin
tm
end
| uu____3953 -> begin
(

let uu____3954 = (FStar_Syntax_Util.head_and_args tm)
in (match (uu____3954) with
| (head1, args) -> begin
(

let uu____3980 = (

let uu____3981 = (FStar_Syntax_Util.un_uinst head1)
in uu____3981.FStar_Syntax_Syntax.n)
in (match (uu____3980) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3985 = (FStar_List.tryFind (fun ps -> (FStar_Syntax_Syntax.fv_eq_lid fv ps.name)) cfg.primitive_steps)
in (match (uu____3985) with
| FStar_Pervasives_Native.None -> begin
tm
end
| FStar_Pervasives_Native.Some (prim_step) -> begin
(match (((FStar_List.length args) < prim_step.arity)) with
| true -> begin
tm
end
| uu____3996 -> begin
(

let uu____3997 = (prim_step.interpretation head1.FStar_Syntax_Syntax.pos args)
in (match (uu____3997) with
| FStar_Pervasives_Native.None -> begin
tm
end
| FStar_Pervasives_Native.Some (reduced) -> begin
reduced
end))
end)
end))
end
| uu____4000 -> begin
tm
end))
end))
end)))


let reduce_equality : cfg  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (reduce_primops (

let uu___158_4007 = cfg
in {steps = (Primops)::[]; tcenv = uu___158_4007.tcenv; delta_level = uu___158_4007.delta_level; primitive_steps = equality_ops}) tm))


let maybe_simplify : cfg  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (

let steps = cfg.steps
in (

let w = (fun t -> (

let uu___159_4029 = t
in {FStar_Syntax_Syntax.n = uu___159_4029.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___159_4029.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___159_4029.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_Pervasives_Native.Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid) -> begin
FStar_Pervasives_Native.Some (false)
end
| uu____4048 -> begin
FStar_Pervasives_Native.None
end))
in (

let simplify = (fun arg -> (((simp_t (FStar_Pervasives_Native.fst arg))), (arg)))
in (

let uu____4075 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps))
in (match (uu____4075) with
| true -> begin
(reduce_primops cfg tm)
end
| uu____4076 -> begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____4078; FStar_Syntax_Syntax.pos = uu____4079; FStar_Syntax_Syntax.vars = uu____4080}, uu____4081); FStar_Syntax_Syntax.tk = uu____4082; FStar_Syntax_Syntax.pos = uu____4083; FStar_Syntax_Syntax.vars = uu____4084}, args) -> begin
(

let uu____4104 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____4104) with
| true -> begin
(

let uu____4105 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____4105) with
| ((FStar_Pervasives_Native.Some (true), uu____4138))::((uu____4139, (arg, uu____4141)))::[] -> begin
arg
end
| ((uu____4182, (arg, uu____4184)))::((FStar_Pervasives_Native.Some (true), uu____4185))::[] -> begin
arg
end
| ((FStar_Pervasives_Native.Some (false), uu____4226))::(uu____4227)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____4265)::((FStar_Pervasives_Native.Some (false), uu____4266))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____4304 -> begin
tm
end))
end
| uu____4313 -> begin
(

let uu____4314 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____4314) with
| true -> begin
(

let uu____4315 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____4315) with
| ((FStar_Pervasives_Native.Some (true), uu____4348))::(uu____4349)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____4387)::((FStar_Pervasives_Native.Some (true), uu____4388))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____4426))::((uu____4427, (arg, uu____4429)))::[] -> begin
arg
end
| ((uu____4470, (arg, uu____4472)))::((FStar_Pervasives_Native.Some (false), uu____4473))::[] -> begin
arg
end
| uu____4514 -> begin
tm
end))
end
| uu____4523 -> begin
(

let uu____4524 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____4524) with
| true -> begin
(

let uu____4525 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____4525) with
| (uu____4558)::((FStar_Pervasives_Native.Some (true), uu____4559))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____4597))::(uu____4598)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____4636))::((uu____4637, (arg, uu____4639)))::[] -> begin
arg
end
| uu____4680 -> begin
tm
end))
end
| uu____4689 -> begin
(

let uu____4690 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____4690) with
| true -> begin
(

let uu____4691 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____4691) with
| ((FStar_Pervasives_Native.Some (true), uu____4724))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____4748))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____4772 -> begin
tm
end))
end
| uu____4781 -> begin
(

let uu____4782 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____4782) with
| true -> begin
(match (args) with
| ((t, uu____4784))::[] -> begin
(

let uu____4797 = (

let uu____4798 = (FStar_Syntax_Subst.compress t)
in uu____4798.FStar_Syntax_Syntax.n)
in (match (uu____4797) with
| FStar_Syntax_Syntax.Tm_abs ((uu____4801)::[], body, uu____4803) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____4829 -> begin
tm
end)
end
| uu____4831 -> begin
tm
end))
end
| ((uu____4832, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4833))))::((t, uu____4835))::[] -> begin
(

let uu____4862 = (

let uu____4863 = (FStar_Syntax_Subst.compress t)
in uu____4863.FStar_Syntax_Syntax.n)
in (match (uu____4862) with
| FStar_Syntax_Syntax.Tm_abs ((uu____4866)::[], body, uu____4868) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____4894 -> begin
tm
end)
end
| uu____4896 -> begin
tm
end))
end
| uu____4897 -> begin
tm
end)
end
| uu____4903 -> begin
(

let uu____4904 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____4904) with
| true -> begin
(match (args) with
| ((t, uu____4906))::[] -> begin
(

let uu____4919 = (

let uu____4920 = (FStar_Syntax_Subst.compress t)
in uu____4920.FStar_Syntax_Syntax.n)
in (match (uu____4919) with
| FStar_Syntax_Syntax.Tm_abs ((uu____4923)::[], body, uu____4925) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____4951 -> begin
tm
end)
end
| uu____4953 -> begin
tm
end))
end
| ((uu____4954, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4955))))::((t, uu____4957))::[] -> begin
(

let uu____4984 = (

let uu____4985 = (FStar_Syntax_Subst.compress t)
in uu____4985.FStar_Syntax_Syntax.n)
in (match (uu____4984) with
| FStar_Syntax_Syntax.Tm_abs ((uu____4988)::[], body, uu____4990) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____5016 -> begin
tm
end)
end
| uu____5018 -> begin
tm
end))
end
| uu____5019 -> begin
tm
end)
end
| uu____5025 -> begin
(reduce_equality cfg tm)
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5027; FStar_Syntax_Syntax.pos = uu____5028; FStar_Syntax_Syntax.vars = uu____5029}, args) -> begin
(

let uu____5045 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____5045) with
| true -> begin
(

let uu____5046 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____5046) with
| ((FStar_Pervasives_Native.Some (true), uu____5079))::((uu____5080, (arg, uu____5082)))::[] -> begin
arg
end
| ((uu____5123, (arg, uu____5125)))::((FStar_Pervasives_Native.Some (true), uu____5126))::[] -> begin
arg
end
| ((FStar_Pervasives_Native.Some (false), uu____5167))::(uu____5168)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____5206)::((FStar_Pervasives_Native.Some (false), uu____5207))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____5245 -> begin
tm
end))
end
| uu____5254 -> begin
(

let uu____5255 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____5255) with
| true -> begin
(

let uu____5256 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____5256) with
| ((FStar_Pervasives_Native.Some (true), uu____5289))::(uu____5290)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____5328)::((FStar_Pervasives_Native.Some (true), uu____5329))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____5367))::((uu____5368, (arg, uu____5370)))::[] -> begin
arg
end
| ((uu____5411, (arg, uu____5413)))::((FStar_Pervasives_Native.Some (false), uu____5414))::[] -> begin
arg
end
| uu____5455 -> begin
tm
end))
end
| uu____5464 -> begin
(

let uu____5465 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____5465) with
| true -> begin
(

let uu____5466 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____5466) with
| (uu____5499)::((FStar_Pervasives_Native.Some (true), uu____5500))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____5538))::(uu____5539)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____5577))::((uu____5578, (arg, uu____5580)))::[] -> begin
arg
end
| uu____5621 -> begin
tm
end))
end
| uu____5630 -> begin
(

let uu____5631 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____5631) with
| true -> begin
(

let uu____5632 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____5632) with
| ((FStar_Pervasives_Native.Some (true), uu____5665))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____5689))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____5713 -> begin
tm
end))
end
| uu____5722 -> begin
(

let uu____5723 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____5723) with
| true -> begin
(match (args) with
| ((t, uu____5725))::[] -> begin
(

let uu____5738 = (

let uu____5739 = (FStar_Syntax_Subst.compress t)
in uu____5739.FStar_Syntax_Syntax.n)
in (match (uu____5738) with
| FStar_Syntax_Syntax.Tm_abs ((uu____5742)::[], body, uu____5744) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____5770 -> begin
tm
end)
end
| uu____5772 -> begin
tm
end))
end
| ((uu____5773, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____5774))))::((t, uu____5776))::[] -> begin
(

let uu____5803 = (

let uu____5804 = (FStar_Syntax_Subst.compress t)
in uu____5804.FStar_Syntax_Syntax.n)
in (match (uu____5803) with
| FStar_Syntax_Syntax.Tm_abs ((uu____5807)::[], body, uu____5809) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____5835 -> begin
tm
end)
end
| uu____5837 -> begin
tm
end))
end
| uu____5838 -> begin
tm
end)
end
| uu____5844 -> begin
(

let uu____5845 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____5845) with
| true -> begin
(match (args) with
| ((t, uu____5847))::[] -> begin
(

let uu____5860 = (

let uu____5861 = (FStar_Syntax_Subst.compress t)
in uu____5861.FStar_Syntax_Syntax.n)
in (match (uu____5860) with
| FStar_Syntax_Syntax.Tm_abs ((uu____5864)::[], body, uu____5866) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____5892 -> begin
tm
end)
end
| uu____5894 -> begin
tm
end))
end
| ((uu____5895, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____5896))))::((t, uu____5898))::[] -> begin
(

let uu____5925 = (

let uu____5926 = (FStar_Syntax_Subst.compress t)
in uu____5926.FStar_Syntax_Syntax.n)
in (match (uu____5925) with
| FStar_Syntax_Syntax.Tm_abs ((uu____5929)::[], body, uu____5931) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____5957 -> begin
tm
end)
end
| uu____5959 -> begin
tm
end))
end
| uu____5960 -> begin
tm
end)
end
| uu____5966 -> begin
(reduce_equality cfg tm)
end))
end))
end))
end))
end))
end))
end
| uu____5967 -> begin
tm
end)
end)))))))


let is_norm_request = (fun hd1 args -> (

let uu____5982 = (

let uu____5986 = (

let uu____5987 = (FStar_Syntax_Util.un_uinst hd1)
in uu____5987.FStar_Syntax_Syntax.n)
in ((uu____5986), (args)))
in (match (uu____5982) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5992)::(uu____5993)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5996)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize)
end
| uu____5998 -> begin
false
end)))


let get_norm_request = (fun args -> (match (args) with
| (uu____6017)::((tm, uu____6019))::[] -> begin
tm
end
| ((tm, uu____6029))::[] -> begin
tm
end
| uu____6034 -> begin
(failwith "Impossible")
end))


let is_reify_head : stack_elt Prims.list  ->  Prims.bool = (fun uu___135_6041 -> (match (uu___135_6041) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____6043; FStar_Syntax_Syntax.pos = uu____6044; FStar_Syntax_Syntax.vars = uu____6045}, uu____6046, uu____6047))::uu____6048 -> begin
true
end
| uu____6054 -> begin
false
end))


let is_fstar_tactics_embed : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____6059 = (

let uu____6060 = (FStar_Syntax_Util.un_uinst t)
in uu____6060.FStar_Syntax_Syntax.n)
in (match (uu____6059) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_tactics_embed_lid)
end
| uu____6064 -> begin
false
end)))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let firstn = (fun k l -> (match (((FStar_List.length l) < k)) with
| true -> begin
((l), ([]))
end
| uu____6176 -> begin
(FStar_Util.first_N k l)
end))
in ((log cfg (fun uu____6178 -> (

let uu____6179 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____6180 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6181 = (

let uu____6182 = (

let uu____6184 = (firstn (Prims.parse_int "4") stack1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6184))
in (stack_to_string uu____6182))
in (FStar_Util.print3 ">>> %s\nNorm %s with top of the stack %s \n" uu____6179 uu____6180 uu____6181))))));
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____6196) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____6217) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_constant (uu____6226) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____6227) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6228; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = uu____6229}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6234; FStar_Syntax_Syntax.fv_delta = uu____6235; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6239; FStar_Syntax_Syntax.fv_delta = uu____6240; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6241))}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____6249; FStar_Syntax_Syntax.pos = uu____6250; FStar_Syntax_Syntax.vars = uu____6251}, uu____6252) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_tactics_embed_lid) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when (is_fstar_tactics_embed hd1) -> begin
(

let args1 = (closures_as_args_delayed cfg env args)
in (

let t2 = (

let uu___160_6292 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd1), (args1))); FStar_Syntax_Syntax.tk = uu___160_6292.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___160_6292.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___160_6292.FStar_Syntax_Syntax.vars})
in (

let t3 = (reduce_primops cfg t2)
in (rebuild cfg env stack1 t3))))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when (((

let uu____6321 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoFullNorm))
in (not (uu____6321))) && (is_norm_request hd1 args)) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid)))) -> begin
(

let tm = (get_norm_request args)
in (

let s = (Reify)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Primops)::[]
in (

let cfg' = (

let uu___161_6334 = cfg
in {steps = s; tcenv = uu___161_6334.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]; primitive_steps = uu___161_6334.primitive_steps})
in (

let stack' = (Debug (t1))::(Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (norm cfg' env stack' tm)))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____6339; FStar_Syntax_Syntax.pos = uu____6340; FStar_Syntax_Syntax.vars = uu____6341}, (a1)::(a2)::rest) -> begin
(

let uu____6375 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6375) with
| (hd1, uu____6386) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), ((a1)::[])))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (norm cfg env stack1 t2)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____6441)); FStar_Syntax_Syntax.tk = uu____6442; FStar_Syntax_Syntax.pos = uu____6443; FStar_Syntax_Syntax.vars = uu____6444}, (a)::[]) when ((FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) && (is_reify_head stack1)) -> begin
(

let uu____6467 = (FStar_List.tl stack1)
in (norm cfg env uu____6467 (FStar_Pervasives_Native.fst a)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____6470; FStar_Syntax_Syntax.pos = uu____6471; FStar_Syntax_Syntax.vars = uu____6472}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let uu____6495 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6495) with
| (reify_head, uu____6506) -> begin
(

let a1 = (

let uu____6522 = (FStar_All.pipe_left FStar_Syntax_Util.unascribe (FStar_Pervasives_Native.fst a))
in (FStar_Syntax_Subst.compress uu____6522))
in (match (a1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____6525)); FStar_Syntax_Syntax.tk = uu____6526; FStar_Syntax_Syntax.pos = uu____6527; FStar_Syntax_Syntax.vars = uu____6528}, (a2)::[]) -> begin
(norm cfg env stack1 (FStar_Pervasives_Native.fst a2))
end
| uu____6553 -> begin
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

let uu____6561 = (mk (FStar_Syntax_Syntax.Tm_type (u1)) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 uu____6561)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let uu____6568 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____6568) with
| true -> begin
(norm cfg env stack1 t')
end
| uu____6569 -> begin
(

let us1 = (

let uu____6571 = (

let uu____6575 = (FStar_List.map (norm_universe cfg env) us)
in ((uu____6575), (t1.FStar_Syntax_Syntax.pos)))
in UnivArgs (uu____6571))
in (

let stack2 = (us1)::stack1
in (norm cfg env stack2 t')))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t1
in (

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun uu___136_6584 -> (match (uu___136_6584) with
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
in (match ((not (should_delta))) with
| true -> begin
(rebuild cfg env stack1 t1)
end
| uu____6586 -> begin
(

let r_env = (

let uu____6588 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv uu____6588))
in (

let uu____6589 = (FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6589) with
| FStar_Pervasives_Native.None -> begin
((log cfg (fun uu____6600 -> (FStar_Util.print "Tm_fvar case 2\n" [])));
(rebuild cfg env stack1 t1);
)
end
| FStar_Pervasives_Native.Some (us, t2) -> begin
((log cfg (fun uu____6606 -> (

let uu____6607 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6608 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____6607 uu____6608)))));
(

let t3 = (

let uu____6610 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))))
in (match (uu____6610) with
| true -> begin
t2
end
| uu____6611 -> begin
(FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) t2)
end))
in (

let n1 = (FStar_List.length us)
in (match ((n1 > (Prims.parse_int "0"))) with
| true -> begin
(match (stack1) with
| (UnivArgs (us', uu____6622))::stack2 -> begin
(

let env1 = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env1 u -> (Univ (u))::env1) env))
in (norm cfg env1 stack2 t3))
end
| uu____6635 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack1 t3)
end
| uu____6636 -> begin
(

let uu____6637 = (

let uu____6638 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" uu____6638))
in (failwith uu____6637))
end)
end
| uu____6643 -> begin
(norm cfg env stack1 t3)
end)));
)
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____6645 = (lookup_bvar env x)
in (match (uu____6645) with
| Univ (uu____6646) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env1, t0, r, fix) -> begin
(match (((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps))))) with
| true -> begin
(

let uu____6661 = (FStar_ST.read r)
in (match (uu____6661) with
| FStar_Pervasives_Native.Some (env2, t') -> begin
((log cfg (fun uu____6680 -> (

let uu____6681 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6682 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" uu____6681 uu____6682)))));
(

let uu____6683 = (

let uu____6684 = (FStar_Syntax_Subst.compress t')
in uu____6684.FStar_Syntax_Syntax.n)
in (match (uu____6683) with
| FStar_Syntax_Syntax.Tm_abs (uu____6687) -> begin
(norm cfg env2 stack1 t')
end
| uu____6702 -> begin
(rebuild cfg env2 stack1 t')
end));
)
end
| FStar_Pervasives_Native.None -> begin
(norm cfg env1 ((MemoLazy (r))::stack1) t0)
end))
end
| uu____6709 -> begin
(norm cfg env1 stack1 t0)
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack1) with
| (UnivArgs (uu____6735))::uu____6736 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (uu____6741))::uu____6742 -> begin
(failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, uu____6748, uu____6749))::stack_rest -> begin
(match (c) with
| Univ (uu____6752) -> begin
(norm cfg ((c)::env) stack_rest t1)
end
| uu____6753 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (uu____6756)::[] -> begin
(match (lopt) with
| FStar_Pervasives_Native.None when (FStar_Options.__unit_tests ()) -> begin
((log cfg (fun uu____6769 -> (

let uu____6770 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____6770))));
(norm cfg ((c)::env) stack_rest body);
)
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (l, cflags)) when (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid)) || (FStar_All.pipe_right cflags (FStar_Util.for_some (fun uu___137_6784 -> (match (uu___137_6784) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____6785 -> begin
false
end))))) -> begin
((log cfg (fun uu____6787 -> (

let uu____6788 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____6788))));
(norm cfg ((c)::env) stack_rest body);
)
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
((log cfg (fun uu____6799 -> (

let uu____6800 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____6800))));
(norm cfg ((c)::env) stack_rest body);
)
end
| uu____6801 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| uu____6808 -> begin
(

let cfg1 = (

let uu___162_6816 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = uu___162_6816.tcenv; delta_level = uu___162_6816.delta_level; primitive_steps = uu___162_6816.primitive_steps})
in (

let uu____6817 = (closure_as_term cfg1 env t1)
in (rebuild cfg1 env stack1 uu____6817)))
end)
end
| (uu____6818)::tl1 -> begin
((log cfg (fun uu____6828 -> (

let uu____6829 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____6829))));
(

let body1 = (mk (FStar_Syntax_Syntax.Tm_abs (((tl1), (body), (lopt)))) t1.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body1));
)
end)
end)
end
| (Steps (s, ps, dl))::stack2 -> begin
(norm (

let uu___163_6853 = cfg
in {steps = s; tcenv = uu___163_6853.tcenv; delta_level = dl; primitive_steps = ps}) env stack2 t1)
end
| (MemoLazy (r))::stack2 -> begin
((set_memo r ((env), (t1)));
(log cfg (fun uu____6866 -> (

let uu____6867 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____6867))));
(norm cfg env stack2 t1);
)
end
| (Debug (uu____6868))::uu____6869 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____6871 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____6871))
end
| uu____6872 -> begin
(

let uu____6873 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____6873) with
| (bs1, body1, opening) -> begin
(

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) -> begin
(

let uu____6902 = (

let uu____6908 = (

let uu____6909 = (

let uu____6910 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____6910))
in (FStar_All.pipe_right uu____6909 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____6908 (fun _0_31 -> FStar_Util.Inl (_0_31))))
in (FStar_All.pipe_right uu____6902 (fun _0_32 -> FStar_Pervasives_Native.Some (_0_32))))
end
| uu____6935 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____6949 -> (Dummy)::env1) env))
in ((log cfg (fun uu____6954 -> (

let uu____6955 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____6955))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___164_6965 = cfg
in (

let uu____6966 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___164_6965.steps; tcenv = uu___164_6965.tcenv; delta_level = uu___164_6965.delta_level; primitive_steps = uu____6966}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Meta (uu____6976))::uu____6977 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____6981 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____6981))
end
| uu____6982 -> begin
(

let uu____6983 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____6983) with
| (bs1, body1, opening) -> begin
(

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) -> begin
(

let uu____7012 = (

let uu____7018 = (

let uu____7019 = (

let uu____7020 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____7020))
in (FStar_All.pipe_right uu____7019 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____7018 (fun _0_33 -> FStar_Util.Inl (_0_33))))
in (FStar_All.pipe_right uu____7012 (fun _0_34 -> FStar_Pervasives_Native.Some (_0_34))))
end
| uu____7045 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7059 -> (Dummy)::env1) env))
in ((log cfg (fun uu____7064 -> (

let uu____7065 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7065))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___164_7075 = cfg
in (

let uu____7076 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___164_7075.steps; tcenv = uu___164_7075.tcenv; delta_level = uu___164_7075.delta_level; primitive_steps = uu____7076}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Let (uu____7086))::uu____7087 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7093 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7093))
end
| uu____7094 -> begin
(

let uu____7095 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7095) with
| (bs1, body1, opening) -> begin
(

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) -> begin
(

let uu____7124 = (

let uu____7130 = (

let uu____7131 = (

let uu____7132 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____7132))
in (FStar_All.pipe_right uu____7131 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____7130 (fun _0_35 -> FStar_Util.Inl (_0_35))))
in (FStar_All.pipe_right uu____7124 (fun _0_36 -> FStar_Pervasives_Native.Some (_0_36))))
end
| uu____7157 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7171 -> (Dummy)::env1) env))
in ((log cfg (fun uu____7176 -> (

let uu____7177 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7177))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___164_7187 = cfg
in (

let uu____7188 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___164_7187.steps; tcenv = uu___164_7187.tcenv; delta_level = uu___164_7187.delta_level; primitive_steps = uu____7188}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (App (uu____7198))::uu____7199 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7204 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7204))
end
| uu____7205 -> begin
(

let uu____7206 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7206) with
| (bs1, body1, opening) -> begin
(

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) -> begin
(

let uu____7235 = (

let uu____7241 = (

let uu____7242 = (

let uu____7243 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____7243))
in (FStar_All.pipe_right uu____7242 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____7241 (fun _0_37 -> FStar_Util.Inl (_0_37))))
in (FStar_All.pipe_right uu____7235 (fun _0_38 -> FStar_Pervasives_Native.Some (_0_38))))
end
| uu____7268 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7282 -> (Dummy)::env1) env))
in ((log cfg (fun uu____7287 -> (

let uu____7288 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7288))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___164_7298 = cfg
in (

let uu____7299 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___164_7298.steps; tcenv = uu___164_7298.tcenv; delta_level = uu___164_7298.delta_level; primitive_steps = uu____7299}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Abs (uu____7309))::uu____7310 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7320 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7320))
end
| uu____7321 -> begin
(

let uu____7322 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7322) with
| (bs1, body1, opening) -> begin
(

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) -> begin
(

let uu____7351 = (

let uu____7357 = (

let uu____7358 = (

let uu____7359 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____7359))
in (FStar_All.pipe_right uu____7358 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____7357 (fun _0_39 -> FStar_Util.Inl (_0_39))))
in (FStar_All.pipe_right uu____7351 (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40))))
end
| uu____7384 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7398 -> (Dummy)::env1) env))
in ((log cfg (fun uu____7403 -> (

let uu____7404 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7404))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___164_7414 = cfg
in (

let uu____7415 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___164_7414.steps; tcenv = uu___164_7414.tcenv; delta_level = uu___164_7414.delta_level; primitive_steps = uu____7415}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| [] -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7425 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7425))
end
| uu____7426 -> begin
(

let uu____7427 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7427) with
| (bs1, body1, opening) -> begin
(

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) -> begin
(

let uu____7456 = (

let uu____7462 = (

let uu____7463 = (

let uu____7464 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____7464))
in (FStar_All.pipe_right uu____7463 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____7462 (fun _0_41 -> FStar_Util.Inl (_0_41))))
in (FStar_All.pipe_right uu____7456 (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42))))
end
| uu____7489 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7503 -> (Dummy)::env1) env))
in ((log cfg (fun uu____7508 -> (

let uu____7509 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7509))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___164_7519 = cfg
in (

let uu____7520 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___164_7519.steps; tcenv = uu___164_7519.tcenv; delta_level = uu___164_7519.delta_level; primitive_steps = uu____7520}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack2 = (FStar_All.pipe_right stack1 (FStar_List.fold_right (fun uu____7552 stack2 -> (match (uu____7552) with
| (a, aq) -> begin
(

let uu____7560 = (

let uu____7561 = (

let uu____7565 = (

let uu____7566 = (

let uu____7576 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____7576), (false)))
in Clos (uu____7566))
in ((uu____7565), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____7561))
in (uu____7560)::stack2)
end)) args))
in ((log cfg (fun uu____7598 -> (

let uu____7599 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____7599))));
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

let uu___165_7620 = x
in {FStar_Syntax_Syntax.ppname = uu___165_7620.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___165_7620.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 t2)))
end
| uu____7621 -> begin
(

let uu____7624 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7624))
end)
end
| uu____7625 -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let uu____7627 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____7627) with
| (closing, f1) -> begin
(

let f2 = (norm cfg ((Dummy)::env) [] f1)
in (

let t2 = (

let uu____7643 = (

let uu____7644 = (

let uu____7649 = (FStar_Syntax_Subst.close closing f2)
in (((

let uu___166_7650 = x
in {FStar_Syntax_Syntax.ppname = uu___166_7650.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___166_7650.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (uu____7649)))
in FStar_Syntax_Syntax.Tm_refine (uu____7644))
in (mk uu____7643 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack1 t2)))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7663 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7663))
end
| uu____7664 -> begin
(

let uu____7665 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7665) with
| (bs1, c1) -> begin
(

let c2 = (

let uu____7671 = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7677 -> (Dummy)::env1) env))
in (norm_comp cfg uu____7671 c1))
in (

let t2 = (

let uu____7684 = (norm_binders cfg env bs1)
in (FStar_Syntax_Util.arrow uu____7684 c2))
in (rebuild cfg env stack1 t2)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) -> begin
(match (stack1) with
| (Match (uu____7727))::uu____7728 -> begin
(norm cfg env stack1 t11)
end
| (Arg (uu____7733))::uu____7734 -> begin
(norm cfg env stack1 t11)
end
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____7739; FStar_Syntax_Syntax.pos = uu____7740; FStar_Syntax_Syntax.vars = uu____7741}, uu____7742, uu____7743))::uu____7744 -> begin
(norm cfg env stack1 t11)
end
| (MemoLazy (uu____7750))::uu____7751 -> begin
(norm cfg env stack1 t11)
end
| uu____7756 -> begin
(

let t12 = (norm cfg env [] t11)
in ((log cfg (fun uu____7759 -> (FStar_Util.print_string "+++ Normalizing ascription \n")));
(

let tc1 = (match (tc) with
| FStar_Util.Inl (t2) -> begin
(

let uu____7772 = (norm cfg env [] t2)
in FStar_Util.Inl (uu____7772))
end
| FStar_Util.Inr (c) -> begin
(

let uu____7780 = (norm_comp cfg env c)
in FStar_Util.Inr (uu____7780))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (norm cfg env []))
in (

let uu____7785 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t12), (((tc1), (tacopt1))), (l)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 uu____7785))));
))
end)
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let stack2 = (Match (((env), (branches), (t1.FStar_Syntax_Syntax.pos))))::stack1
in (norm cfg env stack2 head1))
end
| FStar_Syntax_Syntax.Tm_let ((uu____7836, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____7837); FStar_Syntax_Syntax.lbunivs = uu____7838; FStar_Syntax_Syntax.lbtyp = uu____7839; FStar_Syntax_Syntax.lbeff = uu____7840; FStar_Syntax_Syntax.lbdef = uu____7841})::uu____7842), uu____7843) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n1 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in (

let uu____7869 = ((

let uu____7870 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps))
in (not (uu____7870))) && ((FStar_Syntax_Util.is_pure_effect n1) || ((FStar_Syntax_Util.is_ghost_effect n1) && (

let uu____7871 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (not (uu____7871))))))
in (match (uu____7869) with
| true -> begin
(

let env1 = (

let uu____7874 = (

let uu____7875 = (

let uu____7885 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (uu____7885), (false)))
in Clos (uu____7875))
in (uu____7874)::env)
in (norm cfg env1 stack1 body))
end
| uu____7908 -> begin
(

let uu____7909 = (

let uu____7912 = (

let uu____7913 = (

let uu____7914 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right uu____7914 FStar_Syntax_Syntax.mk_binder))
in (uu____7913)::[])
in (FStar_Syntax_Subst.open_term uu____7912 body))
in (match (uu____7909) with
| (bs, body1) -> begin
(

let lb1 = (

let uu___167_7920 = lb
in (

let uu____7921 = (

let uu____7924 = (

let uu____7925 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____7925 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7924 (fun _0_43 -> FStar_Util.Inl (_0_43))))
in (

let uu____7934 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____7937 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu____7921; FStar_Syntax_Syntax.lbunivs = uu___167_7920.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____7934; FStar_Syntax_Syntax.lbeff = uu___167_7920.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____7937}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env1 uu____7947 -> (Dummy)::env1) env))
in (norm cfg env' ((Let (((env), (bs), (lb1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(

let uu____7963 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7963))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let uu____7976 = (FStar_List.fold_right (fun lb uu____7998 -> (match (uu____7998) with
| (rec_env, memos, i) -> begin
(

let f_i = (

let uu____8037 = (

let uu___168_8038 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___168_8038.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___168_8038.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm uu____8037))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t1.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let rec_env1 = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env1), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (FStar_Pervasives_Native.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (uu____7976) with
| (rec_env, memos, uu____8098) -> begin
(

let uu____8113 = (FStar_List.map2 (fun lb memo -> (FStar_ST.write memo (FStar_Pervasives_Native.Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (FStar_Pervasives_Native.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env1 -> (

let uu____8155 = (

let uu____8156 = (

let uu____8166 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (uu____8166), (false)))
in Clos (uu____8156))
in (uu____8155)::env1)) (FStar_Pervasives_Native.snd lbs) env)
in (norm cfg body_env stack1 body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head1, m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m1, t2) -> begin
(

let should_reify = (match (stack1) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____8204; FStar_Syntax_Syntax.pos = uu____8205; FStar_Syntax_Syntax.vars = uu____8206}, uu____8207, uu____8208))::uu____8209 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____8215 -> begin
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

let uu____8222 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____8222) with
| true -> begin
(

let uu___169_8223 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::(NoDeltaSteps)::[]; tcenv = uu___169_8223.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___169_8223.primitive_steps})
end
| uu____8224 -> begin
(

let uu___170_8225 = cfg
in {steps = (FStar_List.append ((NoDeltaSteps)::(Exclude (Zeta))::[]) cfg.steps); tcenv = uu___170_8225.tcenv; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___170_8225.primitive_steps})
end))
in (norm cfg1 env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m1), (t3)))), (t3.FStar_Syntax_Syntax.pos))))::stack2) head1))))
end
| uu____8226 -> begin
(

let uu____8227 = (

let uu____8228 = (FStar_Syntax_Subst.compress head1)
in uu____8228.FStar_Syntax_Syntax.n)
in (match (uu____8227) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m1)
in (

let uu____8242 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____8242) with
| (uu____8243, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____8247) -> begin
(failwith "Cannot reify a top-level let binding")
end
| FStar_Util.Inl (x) -> begin
(

let is_return = (fun e -> (

let uu____8254 = (

let uu____8255 = (FStar_Syntax_Subst.compress e)
in uu____8255.FStar_Syntax_Syntax.n)
in (match (uu____8254) with
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____8260, uu____8261)) -> begin
(

let uu____8270 = (

let uu____8271 = (FStar_Syntax_Subst.compress e1)
in uu____8271.FStar_Syntax_Syntax.n)
in (match (uu____8270) with
| FStar_Syntax_Syntax.Tm_meta (e2, FStar_Syntax_Syntax.Meta_monadic_lift (uu____8276, msrc, uu____8278)) when (FStar_Syntax_Util.is_pure_effect msrc) -> begin
(

let uu____8287 = (FStar_Syntax_Subst.compress e2)
in FStar_Pervasives_Native.Some (uu____8287))
end
| uu____8288 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____8289 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____8290 = (is_return lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____8290) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let lb1 = (

let uu___171_8294 = lb
in {FStar_Syntax_Syntax.lbname = uu___171_8294.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___171_8294.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___171_8294.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = e})
in (

let uu____8295 = (FStar_List.tl stack1)
in (

let uu____8296 = (

let uu____8297 = (

let uu____8300 = (

let uu____8301 = (

let uu____8309 = (FStar_Syntax_Util.mk_reify body)
in ((((false), ((lb1)::[]))), (uu____8309)))
in FStar_Syntax_Syntax.Tm_let (uu____8301))
in (FStar_Syntax_Syntax.mk uu____8300))
in (uu____8297 FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos))
in (norm cfg env uu____8295 uu____8296))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8326 = (

let uu____8327 = (is_return body)
in (match (uu____8327) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_bvar (y); FStar_Syntax_Syntax.tk = uu____8330; FStar_Syntax_Syntax.pos = uu____8331; FStar_Syntax_Syntax.vars = uu____8332}) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____8337 -> begin
false
end))
in (match (uu____8326) with
| true -> begin
(norm cfg env stack1 lb.FStar_Syntax_Syntax.lbdef)
end
| uu____8339 -> begin
(

let head2 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body1 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify body)
in (

let body2 = (

let uu____8357 = (

let uu____8360 = (

let uu____8361 = (

let uu____8376 = (

let uu____8378 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____8378)::[])
in ((uu____8376), (body1), (FStar_Pervasives_Native.Some (FStar_Util.Inr (((m1), ([])))))))
in FStar_Syntax_Syntax.Tm_abs (uu____8361))
in (FStar_Syntax_Syntax.mk uu____8360))
in (uu____8357 FStar_Pervasives_Native.None body1.FStar_Syntax_Syntax.pos))
in (

let close1 = (closure_as_term cfg env)
in (

let bind_inst = (

let uu____8411 = (

let uu____8412 = (FStar_Syntax_Subst.compress bind_repr)
in uu____8412.FStar_Syntax_Syntax.n)
in (match (uu____8411) with
| FStar_Syntax_Syntax.Tm_uinst (bind1, (uu____8418)::(uu____8419)::[]) -> begin
(

let uu____8425 = (

let uu____8428 = (

let uu____8429 = (

let uu____8434 = (

let uu____8436 = (

let uu____8437 = (close1 lb.FStar_Syntax_Syntax.lbtyp)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____8437))
in (

let uu____8438 = (

let uu____8440 = (

let uu____8441 = (close1 t2)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____8441))
in (uu____8440)::[])
in (uu____8436)::uu____8438))
in ((bind1), (uu____8434)))
in FStar_Syntax_Syntax.Tm_uinst (uu____8429))
in (FStar_Syntax_Syntax.mk uu____8428))
in (uu____8425 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
end
| uu____8453 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let reified = (

let uu____8459 = (

let uu____8462 = (

let uu____8463 = (

let uu____8473 = (

let uu____8475 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____8476 = (

let uu____8478 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____8479 = (

let uu____8481 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____8482 = (

let uu____8484 = (FStar_Syntax_Syntax.as_arg head2)
in (

let uu____8485 = (

let uu____8487 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____8488 = (

let uu____8490 = (FStar_Syntax_Syntax.as_arg body2)
in (uu____8490)::[])
in (uu____8487)::uu____8488))
in (uu____8484)::uu____8485))
in (uu____8481)::uu____8482))
in (uu____8478)::uu____8479))
in (uu____8475)::uu____8476))
in ((bind_inst), (uu____8473)))
in FStar_Syntax_Syntax.Tm_app (uu____8463))
in (FStar_Syntax_Syntax.mk uu____8462))
in (uu____8459 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (

let uu____8502 = (FStar_List.tl stack1)
in (norm cfg env uu____8502 reified))))))))
end))
end)))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head_app, args) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m1)
in (

let uu____8520 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____8520) with
| (uu____8521, bind_repr) -> begin
(

let maybe_unfold_action = (fun head2 -> (

let maybe_extract_fv = (fun t3 -> (

let t4 = (

let uu____8544 = (

let uu____8545 = (FStar_Syntax_Subst.compress t3)
in uu____8545.FStar_Syntax_Syntax.n)
in (match (uu____8544) with
| FStar_Syntax_Syntax.Tm_uinst (t4, uu____8551) -> begin
t4
end
| uu____8556 -> begin
head2
end))
in (

let uu____8557 = (

let uu____8558 = (FStar_Syntax_Subst.compress t4)
in uu____8558.FStar_Syntax_Syntax.n)
in (match (uu____8557) with
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____8563 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____8564 = (maybe_extract_fv head2)
in (match (uu____8564) with
| FStar_Pervasives_Native.Some (x) when (

let uu____8570 = (FStar_Syntax_Syntax.lid_of_fv x)
in (FStar_TypeChecker_Env.is_action cfg.tcenv uu____8570)) -> begin
(

let head3 = (norm cfg env [] head2)
in (

let action_unfolded = (

let uu____8574 = (maybe_extract_fv head3)
in (match (uu____8574) with
| FStar_Pervasives_Native.Some (uu____8577) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____8578 -> begin
FStar_Pervasives_Native.Some (false)
end))
in ((head3), (action_unfolded))))
end
| uu____8581 -> begin
((head2), (FStar_Pervasives_Native.None))
end))))
in ((

let is_arg_impure = (fun uu____8592 -> (match (uu____8592) with
| (e, q) -> begin
(

let uu____8597 = (

let uu____8598 = (FStar_Syntax_Subst.compress e)
in uu____8598.FStar_Syntax_Syntax.n)
in (match (uu____8597) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m11, m2, t')) -> begin
(not ((FStar_Syntax_Util.is_pure_effect m11)))
end
| uu____8613 -> begin
false
end))
end))
in (

let uu____8614 = (

let uu____8615 = (

let uu____8619 = (FStar_Syntax_Syntax.as_arg head_app)
in (uu____8619)::args)
in (FStar_Util.for_some is_arg_impure uu____8615))
in (match (uu____8614) with
| true -> begin
(

let uu____8622 = (

let uu____8623 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format1 "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n" uu____8623))
in (failwith uu____8622))
end
| uu____8624 -> begin
()
end)));
(

let uu____8625 = (maybe_unfold_action head_app)
in (match (uu____8625) with
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

let uu____8660 = (FStar_List.tl stack1)
in (norm cfg env uu____8660 body1)))))
end));
))
end)))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (

let uu____8674 = (closure_as_term cfg env t')
in (reify_lift cfg.tcenv e msrc mtgt uu____8674))
in (

let uu____8675 = (FStar_List.tl stack1)
in (norm cfg env uu____8675 lifted)))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____8758 -> (match (uu____8758) with
| (pat, wopt, tm) -> begin
(

let uu____8796 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____8796)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches1)))) t2.FStar_Syntax_Syntax.pos)
in (

let uu____8822 = (FStar_List.tl stack1)
in (norm cfg env uu____8822 tm))))
end
| uu____8823 -> begin
(norm cfg env stack1 head1)
end))
end))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) -> begin
(

let should_reify = (match (stack1) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____8832; FStar_Syntax_Syntax.pos = uu____8833; FStar_Syntax_Syntax.vars = uu____8834}, uu____8835, uu____8836))::uu____8837 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____8843 -> begin
false
end)
in (match (should_reify) with
| true -> begin
(

let uu____8844 = (FStar_List.tl stack1)
in (

let uu____8845 = (

let uu____8846 = (closure_as_term cfg env t2)
in (reify_lift cfg.tcenv head1 m1 m' uu____8846))
in (norm cfg env uu____8844 uu____8845)))
end
| uu____8847 -> begin
(

let t3 = (norm cfg env [] t2)
in (

let uu____8849 = (((FStar_Syntax_Util.is_pure_effect m1) || (FStar_Syntax_Util.is_ghost_effect m1)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)))
in (match (uu____8849) with
| true -> begin
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___172_8855 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = uu___172_8855.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___172_8855.primitive_steps})
in (norm cfg1 env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t3)))), (head1.FStar_Syntax_Syntax.pos))))::stack2) head1)))
end
| uu____8856 -> begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t3)))), (head1.FStar_Syntax_Syntax.pos))))::stack1) head1)
end)))
end))
end
| uu____8857 -> begin
(match (stack1) with
| (uu____8858)::uu____8859 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____8863) -> begin
(norm cfg env ((Meta (((m), (r))))::stack1) head1)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args1 = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args1)), (t1.FStar_Syntax_Syntax.pos))))::stack1) head1))
end
| uu____8878 -> begin
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

let uu____8888 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (uu____8888))
end
| uu____8895 -> begin
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

let uu____8907 = ed.FStar_Syntax_Syntax.return_repr
in (match (uu____8907) with
| (uu____8908, return_repr) -> begin
(

let return_inst = (

let uu____8915 = (

let uu____8916 = (FStar_Syntax_Subst.compress return_repr)
in uu____8916.FStar_Syntax_Syntax.n)
in (match (uu____8915) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (uu____8922)::[]) -> begin
(

let uu____8928 = (

let uu____8931 = (

let uu____8932 = (

let uu____8937 = (

let uu____8939 = (env.FStar_TypeChecker_Env.universe_of env t)
in (uu____8939)::[])
in ((return_tm), (uu____8937)))
in FStar_Syntax_Syntax.Tm_uinst (uu____8932))
in (FStar_Syntax_Syntax.mk uu____8931))
in (uu____8928 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end
| uu____8951 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let uu____8954 = (

let uu____8957 = (

let uu____8958 = (

let uu____8968 = (

let uu____8970 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____8971 = (

let uu____8973 = (FStar_Syntax_Syntax.as_arg e)
in (uu____8973)::[])
in (uu____8970)::uu____8971))
in ((return_inst), (uu____8968)))
in FStar_Syntax_Syntax.Tm_app (uu____8958))
in (FStar_Syntax_Syntax.mk uu____8957))
in (uu____8954 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end)))
end
| uu____8985 -> begin
(

let uu____8986 = (FStar_TypeChecker_Env.monad_leq env msrc mtgt)
in (match (uu____8986) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8988 = (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" (FStar_Ident.text_of_lid msrc) (FStar_Ident.text_of_lid mtgt))
in (failwith uu____8988))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____8989; FStar_TypeChecker_Env.mtarget = uu____8990; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____8991; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(failwith "Impossible : trying to reify a non-reifiable lift (from %s to %s)")
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____9002; FStar_TypeChecker_Env.mtarget = uu____9003; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____9004; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let uu____9022 = (FStar_Syntax_Util.mk_reify e)
in (lift t FStar_Syntax_Syntax.tun uu____9022))
end))
end))
and norm_pattern_args : cfg  ->  env  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun uu____9052 -> (match (uu____9052) with
| (a, imp) -> begin
(

let uu____9059 = (norm cfg env [] a)
in ((uu____9059), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp1 = (ghost_to_pure_aux cfg env comp)
in (match (comp1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu___173_9074 = comp1
in (

let uu____9077 = (

let uu____9078 = (

let uu____9084 = (norm cfg env [] t)
in (

let uu____9085 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____9084), (uu____9085))))
in FStar_Syntax_Syntax.Total (uu____9078))
in {FStar_Syntax_Syntax.n = uu____9077; FStar_Syntax_Syntax.tk = uu___173_9074.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___173_9074.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___173_9074.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu___174_9100 = comp1
in (

let uu____9103 = (

let uu____9104 = (

let uu____9110 = (norm cfg env [] t)
in (

let uu____9111 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____9110), (uu____9111))))
in FStar_Syntax_Syntax.GTotal (uu____9104))
in {FStar_Syntax_Syntax.n = uu____9103; FStar_Syntax_Syntax.tk = uu___174_9100.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___174_9100.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___174_9100.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____9142 -> (match (uu____9142) with
| (a, i) -> begin
(

let uu____9149 = (norm cfg env [] a)
in ((uu____9149), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___138_9154 -> (match (uu___138_9154) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____9158 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____9158))
end
| f -> begin
f
end))))
in (

let uu___175_9162 = comp1
in (

let uu____9165 = (

let uu____9166 = (

let uu___176_9167 = ct
in (

let uu____9168 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (

let uu____9169 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____9172 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = uu____9168; FStar_Syntax_Syntax.effect_name = uu___176_9167.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____9169; FStar_Syntax_Syntax.effect_args = uu____9172; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (uu____9166))
in {FStar_Syntax_Syntax.n = uu____9165; FStar_Syntax_Syntax.tk = uu___175_9162.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___175_9162.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___175_9162.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm1 = (fun t -> (norm (

let uu___177_9189 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = uu___177_9189.tcenv; delta_level = uu___177_9189.delta_level; primitive_steps = uu___177_9189.primitive_steps}) env [] t))
in (

let non_info = (fun t -> (

let uu____9194 = (norm1 t)
in (FStar_Syntax_Util.non_informative uu____9194)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____9197) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let uu___178_9211 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = uu___178_9211.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___178_9211.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___178_9211.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____9221 = ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ))
in (match (uu____9221) with
| true -> begin
(

let ct1 = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let uu___179_9226 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___179_9226.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = uu___179_9226.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___179_9226.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___179_9226.FStar_Syntax_Syntax.flags})
end
| FStar_Pervasives_Native.None -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c)
in (

let uu___180_9228 = ct1
in {FStar_Syntax_Syntax.comp_univs = uu___180_9228.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu___180_9228.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___180_9228.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___180_9228.FStar_Syntax_Syntax.flags}))
end)
in (

let uu___181_9229 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.tk = uu___181_9229.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___181_9229.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___181_9229.FStar_Syntax_Syntax.vars}))
end
| uu____9234 -> begin
c
end)))
end
| uu____9235 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env uu____9238 -> (match (uu____9238) with
| (x, imp) -> begin
(

let uu____9241 = (

let uu___182_9242 = x
in (

let uu____9243 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___182_9242.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___182_9242.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____9243}))
in ((uu____9241), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let uu____9249 = (FStar_List.fold_left (fun uu____9256 b -> (match (uu____9256) with
| (nbs', env1) -> begin
(

let b1 = (norm_binder cfg env1 b)
in (((b1)::nbs'), ((Dummy)::env1)))
end)) (([]), (env)) bs)
in (match (uu____9249) with
| (nbs, uu____9273) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) -> begin
(

let flags = (filter_out_lcomp_cflags lc)
in (

let uu____9290 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____9290) with
| true -> begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____9295 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____9295) with
| true -> begin
(

let uu____9299 = (

let uu____9302 = (

let uu____9303 = (

let uu____9306 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.comp_set_flags uu____9306 flags))
in (FStar_Syntax_Util.lcomp_of_comp uu____9303))
in FStar_Util.Inl (uu____9302))
in FStar_Pervasives_Native.Some (uu____9299))
end
| uu____9309 -> begin
(

let uu____9310 = (

let uu____9313 = (

let uu____9314 = (

let uu____9317 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.comp_set_flags uu____9317 flags))
in (FStar_Syntax_Util.lcomp_of_comp uu____9314))
in FStar_Util.Inl (uu____9313))
in FStar_Pervasives_Native.Some (uu____9310))
end)))
end
| uu____9320 -> begin
FStar_Pervasives_Native.Some (FStar_Util.Inr (((lc.FStar_Syntax_Syntax.eff_name), (flags))))
end)))
end
| uu____9330 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 t -> (match (stack1) with
| [] -> begin
t
end
| (Debug (tm))::stack2 -> begin
((

let uu____9342 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms")))
in (match (uu____9342) with
| true -> begin
(

let uu____9343 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____9344 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Normalized %s to %s\n" uu____9343 uu____9344)))
end
| uu____9345 -> begin
()
end));
(rebuild cfg env stack2 t);
)
end
| (Steps (s, ps, dl))::stack2 -> begin
(rebuild (

let uu___183_9355 = cfg
in {steps = s; tcenv = uu___183_9355.tcenv; delta_level = dl; primitive_steps = ps}) env stack2 t)
end
| (Meta (m, r))::stack2 -> begin
(

let t1 = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack2 t1))
end
| (MemoLazy (r))::stack2 -> begin
((set_memo r ((env), (t)));
(log cfg (fun uu____9375 -> (

let uu____9376 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" uu____9376))));
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

let uu____9413 = (

let uu___184_9414 = (FStar_Syntax_Util.abs bs1 t lopt1)
in {FStar_Syntax_Syntax.n = uu___184_9414.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___184_9414.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___184_9414.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack2 uu____9413))))
end
| (Arg (Univ (uu____9419), uu____9420, uu____9421))::uu____9422 -> begin
(failwith "Impossible")
end
| (Arg (Dummy, uu____9424, uu____9425))::uu____9426 -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack2 -> begin
(

let t1 = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack2 t1))
end
| (Arg (Clos (env1, tm, m, uu____9438), aq, r))::stack2 -> begin
((log cfg (fun uu____9454 -> (

let uu____9455 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" uu____9455))));
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
| uu____9462 -> begin
(

let stack3 = (App (((t), (aq), (r))))::stack2
in (norm cfg env1 stack3 tm))
end)
end
| uu____9465 -> begin
(

let uu____9466 = (FStar_ST.read m)
in (match (uu____9466) with
| FStar_Pervasives_Native.None -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let arg = (closure_as_term cfg env1 tm)
in (

let t1 = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack2 t1)))
end
| uu____9486 -> begin
(

let stack3 = (MemoLazy (m))::(App (((t), (aq), (r))))::stack2
in (norm cfg env1 stack3 tm))
end)
end
| FStar_Pervasives_Native.Some (uu____9492, a) -> begin
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

let uu____9514 = (maybe_simplify cfg t1)
in (rebuild cfg env stack2 uu____9514)))
end
| (Match (env1, branches, r))::stack2 -> begin
((log cfg (fun uu____9521 -> (

let uu____9522 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" uu____9522))));
(

let scrutinee = t
in (

let norm_and_rebuild_match = (fun uu____9527 -> ((log cfg (fun uu____9529 -> (

let uu____9530 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____9531 = (

let uu____9532 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____9539 -> (match (uu____9539) with
| (p, uu____9545, uu____9546) -> begin
(FStar_Syntax_Print.pat_to_string p)
end))))
in (FStar_All.pipe_right uu____9532 (FStar_String.concat "\n\t")))
in (FStar_Util.print2 "match is irreducible: scrutinee=%s\nbranches=%s\n" uu____9530 uu____9531)))));
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg_exclude_iota_zeta = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun uu___139_9556 -> (match (uu___139_9556) with
| FStar_TypeChecker_Env.Inlining -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| uu____9557 -> begin
false
end))))
in (

let steps' = (

let uu____9560 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____9560) with
| true -> begin
(Exclude (Zeta))::[]
end
| uu____9562 -> begin
(Exclude (Iota))::(Exclude (Zeta))::[]
end))
in (

let uu___185_9563 = cfg
in {steps = (FStar_List.append steps' cfg.steps); tcenv = uu___185_9563.tcenv; delta_level = new_delta; primitive_steps = uu___185_9563.primitive_steps})))
in (

let norm_or_whnf = (fun env2 t1 -> (match (whnf) with
| true -> begin
(closure_as_term cfg_exclude_iota_zeta env2 t1)
end
| uu____9573 -> begin
(norm cfg_exclude_iota_zeta env2 [] t1)
end))
in (

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____9597) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____9613 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____9647 uu____9648 -> (match (((uu____9647), (uu____9648))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____9713 = (norm_pat env3 p1)
in (match (uu____9713) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____9613) with
| (pats1, env3) -> begin
(((

let uu___186_9779 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.ty = uu___186_9779.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___186_9779.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___187_9793 = x
in (

let uu____9794 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___187_9793.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___187_9793.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____9794}))
in (((

let uu___188_9800 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.ty = uu___188_9800.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___188_9800.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___189_9805 = x
in (

let uu____9806 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___189_9805.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___189_9805.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____9806}))
in (((

let uu___190_9812 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.ty = uu___190_9812.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___190_9812.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t1) -> begin
(

let x1 = (

let uu___191_9822 = x
in (

let uu____9823 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___191_9822.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___191_9822.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____9823}))
in (

let t2 = (norm_or_whnf env2 t1)
in (((

let uu___192_9830 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t2))); FStar_Syntax_Syntax.ty = uu___192_9830.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___192_9830.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let branches1 = (match (env1) with
| [] when whnf -> begin
branches
end
| uu____9834 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch1 -> (

let uu____9837 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____9837) with
| (p, wopt, e) -> begin
(

let uu____9855 = (norm_pat env1 p)
in (match (uu____9855) with
| (p1, env2) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____9879 = (norm_or_whnf env2 w)
in FStar_Pervasives_Native.Some (uu____9879))
end)
in (

let e1 = (norm_or_whnf env2 e)
in (FStar_Syntax_Util.branch ((p1), (wopt1), (e1)))))
end))
end)))))
end)
in (

let uu____9884 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches1)))) r)
in (rebuild cfg env1 stack2 uu____9884)))))));
))
in (

let rec is_cons = (fun head1 -> (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, uu____9894) -> begin
(is_cons h)
end
| FStar_Syntax_Syntax.Tm_constant (uu____9899) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____9900; FStar_Syntax_Syntax.fv_delta = uu____9901; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____9905; FStar_Syntax_Syntax.fv_delta = uu____9906; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____9907))}) -> begin
true
end
| uu____9914 -> begin
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

let rec matches_pat = (fun scrutinee1 p -> (

let scrutinee2 = (FStar_Syntax_Util.unmeta scrutinee1)
in (

let uu____10013 = (FStar_Syntax_Util.head_and_args scrutinee2)
in (match (uu____10013) with
| (head1, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____10045) -> begin
FStar_Util.Inl ((scrutinee2)::[])
end
| FStar_Syntax_Syntax.Pat_wild (uu____10047) -> begin
FStar_Util.Inl ((scrutinee2)::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____10049) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| uu____10061 -> begin
(

let uu____10062 = (

let uu____10063 = (is_cons head1)
in (not (uu____10063)))
in FStar_Util.Inr (uu____10062))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let uu____10077 = (

let uu____10078 = (FStar_Syntax_Util.un_uinst head1)
in uu____10078.FStar_Syntax_Syntax.n)
in (match (uu____10077) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| uu____10085 -> begin
(

let uu____10086 = (

let uu____10087 = (is_cons head1)
in (not (uu____10087)))
in FStar_Util.Inr (uu____10086))
end))
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t1, uu____10121))::rest_a, ((p1, uu____10124))::rest_p) -> begin
(

let uu____10152 = (matches_pat t1 p1)
in (match (uu____10152) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____10166 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee1 p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p1, wopt, b))::rest -> begin
(

let uu____10237 = (matches_pat scrutinee1 p1)
in (match (uu____10237) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee1 rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
((log cfg (fun uu____10247 -> (

let uu____10248 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____10249 = (

let uu____10250 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right uu____10250 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" uu____10248 uu____10249)))));
(

let env2 = (FStar_List.fold_left (fun env2 t1 -> (

let uu____10259 = (

let uu____10260 = (

let uu____10270 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ((([]), (t1)))))
in (([]), (t1), (uu____10270), (false)))
in Clos (uu____10260))
in (uu____10259)::env2)) env1 s)
in (

let uu____10293 = (guard_when_clause wopt b rest)
in (norm cfg env2 stack2 uu____10293)));
)
end))
end))
in (

let uu____10294 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota))))
in (match (uu____10294) with
| true -> begin
(norm_and_rebuild_match ())
end
| uu____10295 -> begin
(matches scrutinee branches)
end))))))));
)
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun uu___140_10308 -> (match (uu___140_10308) with
| UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| Inlining -> begin
(FStar_TypeChecker_Env.Inlining)::[]
end
| uu____10311 -> begin
[]
end))))
in (

let d1 = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| uu____10315 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d1; primitive_steps = (FStar_List.append built_in_primitive_steps equality_ops)})))


let normalize_with_primitive_steps : primitive_step Prims.list  ->  step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun ps s e t -> (

let c = (config s e)
in (

let c1 = (

let uu___193_10335 = (config s e)
in {steps = uu___193_10335.steps; tcenv = uu___193_10335.tcenv; delta_level = uu___193_10335.delta_level; primitive_steps = (FStar_List.append c.primitive_steps ps)})
in (norm c1 [] [] t))))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (normalize_with_primitive_steps [] s e t))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (

let uu____10354 = (config s e)
in (norm_comp uu____10354 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let uu____10361 = (config [] env)
in (norm_universe uu____10361 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (

let uu____10368 = (config [] env)
in (ghost_to_pure_aux uu____10368 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (

let uu____10380 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____10380)))
in (

let uu____10381 = ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ))
in (match (uu____10381) with
| true -> begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let uu___194_10383 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = uu___194_10383.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___194_10383.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____10384 -> (

let uu____10385 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env uu____10385)))})
end
| FStar_Pervasives_Native.None -> begin
lc
end)
end
| uu____10386 -> begin
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

let uu____10398 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_warning "Normalization failed with error %s" uu____10398));
t;
)
end
in (FStar_Syntax_Print.term_to_string t1)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let c1 = try
(match (()) with
| () -> begin
(

let uu____10407 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp uu____10407 [] c))
end)
with
| e -> begin
((

let uu____10411 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_warning "Normalization failed with error %s" uu____10411));
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

let uu____10448 = (

let uu____10449 = (

let uu____10454 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (uu____10454)))
in FStar_Syntax_Syntax.Tm_refine (uu____10449))
in (mk uu____10448 t01.FStar_Syntax_Syntax.pos))
end
| uu____10459 -> begin
t2
end))
end
| uu____10460 -> begin
t2
end)))
in (aux t))))


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((WHNF)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Beta)::[]) env t))


let reduce_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((Beta)::(NoDeltaSteps)::(CompressUvars)::(Exclude (Zeta))::(Exclude (Iota))::(NoFullNorm)::[]) env t))


let eta_expand_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e t_e -> (

let uu____10482 = (FStar_Syntax_Util.arrow_formals_comp t_e)
in (match (uu____10482) with
| (formals, c) -> begin
(match (formals) with
| [] -> begin
e
end
| uu____10498 -> begin
(

let uu____10502 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____10502) with
| (actuals, uu____10513, uu____10514) -> begin
(match (((FStar_List.length actuals) = (FStar_List.length formals))) with
| true -> begin
e
end
| uu____10535 -> begin
(

let uu____10536 = (FStar_All.pipe_right formals FStar_Syntax_Util.args_of_binders)
in (match (uu____10536) with
| (binders, args) -> begin
(

let uu____10546 = (FStar_Syntax_Syntax.mk_Tm_app e args FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____10549 = (

let uu____10556 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_44 -> FStar_Util.Inl (_0_44)))
in (FStar_All.pipe_right uu____10556 (fun _0_45 -> FStar_Pervasives_Native.Some (_0_45))))
in (FStar_Syntax_Util.abs binders uu____10546 uu____10549)))
end))
end)
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____10592 = (

let uu____10596 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((uu____10596), (t.FStar_Syntax_Syntax.n)))
in (match (uu____10592) with
| (FStar_Pervasives_Native.Some (sort), uu____10603) -> begin
(

let uu____10605 = (mk sort t.FStar_Syntax_Syntax.pos)
in (eta_expand_with_type env t uu____10605))
end
| (uu____10606, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(eta_expand_with_type env t x.FStar_Syntax_Syntax.sort)
end
| uu____10610 -> begin
(

let uu____10614 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____10614) with
| (head1, args) -> begin
(

let uu____10640 = (

let uu____10641 = (FStar_Syntax_Subst.compress head1)
in uu____10641.FStar_Syntax_Syntax.n)
in (match (uu____10640) with
| FStar_Syntax_Syntax.Tm_uvar (uu____10644, thead) -> begin
(

let uu____10658 = (FStar_Syntax_Util.arrow_formals thead)
in (match (uu____10658) with
| (formals, tres) -> begin
(match (((FStar_List.length formals) = (FStar_List.length args))) with
| true -> begin
t
end
| uu____10688 -> begin
(

let uu____10689 = (env.FStar_TypeChecker_Env.type_of (

let uu___199_10693 = env
in {FStar_TypeChecker_Env.solver = uu___199_10693.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___199_10693.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___199_10693.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___199_10693.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___199_10693.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___199_10693.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___199_10693.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___199_10693.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___199_10693.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___199_10693.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___199_10693.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___199_10693.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___199_10693.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___199_10693.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___199_10693.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___199_10693.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___199_10693.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___199_10693.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___199_10693.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___199_10693.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___199_10693.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (uu____10689) with
| (uu____10694, ty, uu____10696) -> begin
(eta_expand_with_type env t ty)
end))
end)
end))
end
| uu____10697 -> begin
(

let uu____10698 = (env.FStar_TypeChecker_Env.type_of (

let uu___200_10702 = env
in {FStar_TypeChecker_Env.solver = uu___200_10702.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___200_10702.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___200_10702.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___200_10702.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___200_10702.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___200_10702.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___200_10702.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___200_10702.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___200_10702.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___200_10702.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___200_10702.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___200_10702.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___200_10702.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___200_10702.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___200_10702.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___200_10702.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___200_10702.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___200_10702.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___200_10702.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___200_10702.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___200_10702.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (uu____10698) with
| (uu____10703, ty, uu____10705) -> begin
(eta_expand_with_type env t ty)
end))
end))
end))
end)))




