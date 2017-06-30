
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

let string_as_const = (fun p b -> (const_as_tm (FStar_Const.Const_string ((((FStar_Util.bytes_of_string b)), (p)))) p))
in (

let arg_as_int = (fun uu____2441 -> (match (uu____2441) with
| (a, uu____2446) -> begin
(

let uu____2448 = (

let uu____2449 = (FStar_Syntax_Subst.compress a)
in uu____2449.FStar_Syntax_Syntax.n)
in (match (uu____2448) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, FStar_Pervasives_Native.None)) -> begin
(

let uu____2459 = (FStar_Util.int_of_string i)
in FStar_Pervasives_Native.Some (uu____2459))
end
| uu____2460 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_bounded_int = (fun uu____2469 -> (match (uu____2469) with
| (a, uu____2476) -> begin
(

let uu____2480 = (

let uu____2481 = (FStar_Syntax_Subst.compress a)
in uu____2481.FStar_Syntax_Syntax.n)
in (match (uu____2480) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv1); FStar_Syntax_Syntax.tk = uu____2488; FStar_Syntax_Syntax.pos = uu____2489; FStar_Syntax_Syntax.vars = uu____2490}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, FStar_Pervasives_Native.None)); FStar_Syntax_Syntax.tk = uu____2492; FStar_Syntax_Syntax.pos = uu____2493; FStar_Syntax_Syntax.vars = uu____2494}, uu____2495))::[]) when (FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") -> begin
(

let uu____2526 = (

let uu____2529 = (FStar_Util.int_of_string i)
in ((fv1), (uu____2529)))
in FStar_Pervasives_Native.Some (uu____2526))
end
| uu____2532 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_bool = (fun uu____2541 -> (match (uu____2541) with
| (a, uu____2546) -> begin
(

let uu____2548 = (

let uu____2549 = (FStar_Syntax_Subst.compress a)
in uu____2549.FStar_Syntax_Syntax.n)
in (match (uu____2548) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (b)) -> begin
FStar_Pervasives_Native.Some (b)
end
| uu____2554 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_char = (fun uu____2561 -> (match (uu____2561) with
| (a, uu____2566) -> begin
(

let uu____2568 = (

let uu____2569 = (FStar_Syntax_Subst.compress a)
in uu____2569.FStar_Syntax_Syntax.n)
in (match (uu____2568) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c)) -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____2574 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_string = (fun uu____2581 -> (match (uu____2581) with
| (a, uu____2586) -> begin
(

let uu____2588 = (

let uu____2589 = (FStar_Syntax_Subst.compress a)
in uu____2589.FStar_Syntax_Syntax.n)
in (match (uu____2588) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (bytes, uu____2594)) -> begin
FStar_Pervasives_Native.Some ((FStar_Util.string_of_bytes bytes))
end
| uu____2597 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let arg_as_list = (fun f uu____2618 -> (match (uu____2618) with
| (a, uu____2627) -> begin
(

let rec sequence = (fun l -> (match (l) with
| [] -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Pervasives_Native.None)::uu____2646 -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.Some (x))::xs -> begin
(

let uu____2656 = (sequence xs)
in (match (uu____2656) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (xs') -> begin
FStar_Pervasives_Native.Some ((x)::xs')
end))
end))
in (

let uu____2667 = (FStar_Syntax_Util.list_elements a)
in (match (uu____2667) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (elts) -> begin
(

let uu____2677 = (FStar_List.map (fun x -> (

let uu____2682 = (FStar_Syntax_Syntax.as_arg x)
in (f uu____2682))) elts)
in (sequence uu____2677))
end)))
end))
in (

let lift_unary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a))::[] -> begin
(

let uu____2712 = (f a)
in FStar_Pervasives_Native.Some (uu____2712))
end
| uu____2713 -> begin
FStar_Pervasives_Native.None
end))
in (

let lift_binary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a0))::(FStar_Pervasives_Native.Some (a1))::[] -> begin
(

let uu____2752 = (f a0 a1)
in FStar_Pervasives_Native.Some (uu____2752))
end
| uu____2753 -> begin
FStar_Pervasives_Native.None
end))
in (

let unary_op = (fun as_a f r args -> (

let uu____2797 = (FStar_List.map as_a args)
in (lift_unary (f r) uu____2797)))
in (

let binary_op = (fun as_a f r args -> (

let uu____2847 = (FStar_List.map as_a args)
in (lift_binary (f r) uu____2847)))
in (

let as_primitive_step = (fun uu____2864 -> (match (uu____2864) with
| (l, arity, f) -> begin
{name = l; arity = arity; strong_reduction_ok = true; interpretation = f}
end))
in (

let unary_int_op = (fun f -> (unary_op arg_as_int (fun r x -> (

let uu____2902 = (f x)
in (int_as_const r uu____2902)))))
in (

let binary_int_op = (fun f -> (binary_op arg_as_int (fun r x y -> (

let uu____2925 = (f x y)
in (int_as_const r uu____2925)))))
in (

let unary_bool_op = (fun f -> (unary_op arg_as_bool (fun r x -> (

let uu____2942 = (f x)
in (bool_as_const r uu____2942)))))
in (

let binary_bool_op = (fun f -> (binary_op arg_as_bool (fun r x y -> (

let uu____2965 = (f x y)
in (bool_as_const r uu____2965)))))
in (

let binary_string_op = (fun f -> (binary_op arg_as_string (fun r x y -> (

let uu____2988 = (f x y)
in (string_as_const r uu____2988)))))
in (

let list_of_string' = (fun rng s -> (

let name = (fun l -> (

let uu____3002 = (

let uu____3003 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____3003))
in (mk uu____3002 rng)))
in (

let char_t = (name FStar_Parser_Const.char_lid)
in (

let charterm = (fun c -> (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))) rng))
in (

let uu____3013 = (

let uu____3015 = (FStar_String.list_of_string s)
in (FStar_List.map charterm uu____3015))
in (FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3013))))))
in (

let string_of_list' = (fun rng l -> (

let s = (FStar_String.string_of_list l)
in (FStar_Syntax_Util.exp_string s)))
in (

let string_of_int1 = (fun rng i -> (

let uu____3037 = (FStar_Util.string_of_int i)
in (string_as_const rng uu____3037)))
in (

let string_of_bool1 = (fun rng b -> (string_as_const rng (match (b) with
| true -> begin
"true"
end
| uu____3045 -> begin
"false"
end)))
in (

let string_of_int2 = (fun rng i -> (

let uu____3053 = (FStar_Util.string_of_int i)
in (string_as_const rng uu____3053)))
in (

let string_of_bool2 = (fun rng b -> (string_as_const rng (match (b) with
| true -> begin
"true"
end
| uu____3061 -> begin
"false"
end)))
in (

let basic_ops = (

let uu____3072 = (

let uu____3082 = (

let uu____3092 = (

let uu____3102 = (

let uu____3112 = (

let uu____3122 = (

let uu____3132 = (

let uu____3142 = (

let uu____3152 = (

let uu____3162 = (

let uu____3172 = (

let uu____3182 = (

let uu____3192 = (

let uu____3202 = (

let uu____3212 = (

let uu____3222 = (

let uu____3232 = (

let uu____3241 = (FStar_Parser_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((uu____3241), ((Prims.parse_int "1")), ((unary_op arg_as_string list_of_string'))))
in (

let uu____3247 = (

let uu____3257 = (

let uu____3266 = (FStar_Parser_Const.p2l (("FStar")::("String")::("string_of_list")::[]))
in ((uu____3266), ((Prims.parse_int "1")), ((unary_op (arg_as_list arg_as_char) string_of_list'))))
in (uu____3257)::[])
in (uu____3232)::uu____3247))
in (((FStar_Parser_Const.string_of_bool_lid), ((Prims.parse_int "1")), ((unary_op arg_as_bool string_of_bool2))))::uu____3222)
in (((FStar_Parser_Const.string_of_int_lid), ((Prims.parse_int "1")), ((unary_op arg_as_int string_of_int2))))::uu____3212)
in (((FStar_Parser_Const.strcat_lid), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____3202)
in (((FStar_Parser_Const.op_Or), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x || y))))))::uu____3192)
in (((FStar_Parser_Const.op_And), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x && y))))))::uu____3182)
in (((FStar_Parser_Const.op_Negation), ((Prims.parse_int "1")), ((unary_bool_op (fun x -> (not (x)))))))::uu____3172)
in (((FStar_Parser_Const.op_Modulus), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x mod y))))))::uu____3162)
in (((FStar_Parser_Const.op_GTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x >= y)))))))::uu____3152)
in (((FStar_Parser_Const.op_GT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x > y)))))))::uu____3142)
in (((FStar_Parser_Const.op_LTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x <= y)))))))::uu____3132)
in (((FStar_Parser_Const.op_LT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (bool_as_const r (x < y)))))))::uu____3122)
in (((FStar_Parser_Const.op_Division), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x / y))))))::uu____3112)
in (((FStar_Parser_Const.op_Multiply), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x * y))))))::uu____3102)
in (((FStar_Parser_Const.op_Subtraction), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x - y))))))::uu____3092)
in (((FStar_Parser_Const.op_Addition), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (x + y))))))::uu____3082)
in (((FStar_Parser_Const.op_Minus), ((Prims.parse_int "1")), ((unary_int_op (fun x -> (~- (x)))))))::uu____3072)
in (

let bounded_arith_ops = (

let bounded_int_types = ("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]
in (

let int_as_bounded = (fun r int_to_t1 n1 -> (

let c = (int_as_const r n1)
in (

let int_to_t2 = (FStar_Syntax_Syntax.fv_to_tm int_to_t1)
in (

let uu____3561 = (

let uu____3562 = (

let uu____3563 = (FStar_Syntax_Syntax.as_arg c)
in (uu____3563)::[])
in (FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3562))
in (uu____3561 FStar_Pervasives_Native.None r)))))
in (FStar_All.pipe_right bounded_int_types (FStar_List.collect (fun m -> (

let uu____3587 = (

let uu____3596 = (FStar_Parser_Const.p2l (("FStar")::(m)::("add")::[]))
in ((uu____3596), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____3605 uu____3606 -> (match (((uu____3605), (uu____3606))) with
| ((int_to_t1, x), (uu____3617, y)) -> begin
(int_as_bounded r int_to_t1 (x + y))
end))))))
in (

let uu____3623 = (

let uu____3633 = (

let uu____3642 = (FStar_Parser_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((uu____3642), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____3651 uu____3652 -> (match (((uu____3651), (uu____3652))) with
| ((int_to_t1, x), (uu____3663, y)) -> begin
(int_as_bounded r int_to_t1 (x - y))
end))))))
in (

let uu____3669 = (

let uu____3679 = (

let uu____3688 = (FStar_Parser_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((uu____3688), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____3697 uu____3698 -> (match (((uu____3697), (uu____3698))) with
| ((int_to_t1, x), (uu____3709, y)) -> begin
(int_as_bounded r int_to_t1 (x * y))
end))))))
in (uu____3679)::[])
in (uu____3633)::uu____3669))
in (uu____3587)::uu____3623)))))))
in (FStar_List.map as_primitive_step (FStar_List.append basic_ops bounded_arith_ops))))))))))))))))))))))))))))))


let equality_ops : primitive_step Prims.list = (

let interp_bool = (fun rng args -> (match (args) with
| ((_typ, uu____3775))::((a1, uu____3777))::((a2, uu____3779))::[] -> begin
(

let uu____3808 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____3808) with
| FStar_Syntax_Util.Equal -> begin
(

let uu____3810 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) rng)
in FStar_Pervasives_Native.Some (uu____3810))
end
| FStar_Syntax_Util.NotEqual -> begin
(

let uu____3815 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) rng)
in FStar_Pervasives_Native.Some (uu____3815))
end
| uu____3820 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____3821 -> begin
(failwith "Unexpected number of arguments")
end))
in (

let interp_prop = (fun r args -> (match (args) with
| ((_typ, uu____3834))::((a1, uu____3836))::((a2, uu____3838))::[] -> begin
(

let uu____3867 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____3867) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___156_3871 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___156_3871.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___156_3871.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___156_3871.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___157_3878 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___157_3878.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___157_3878.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___157_3878.FStar_Syntax_Syntax.vars}))
end
| uu____3883 -> begin
FStar_Pervasives_Native.None
end))
end
| ((_typ, uu____3885))::(uu____3886)::((a1, uu____3888))::((a2, uu____3890))::[] -> begin
(

let uu____3927 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____3927) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___156_3931 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___156_3931.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___156_3931.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___156_3931.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___157_3938 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___157_3938.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___157_3938.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___157_3938.FStar_Syntax_Syntax.vars}))
end
| uu____3943 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____3944 -> begin
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

let uu____3955 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops cfg.steps))
in (match (uu____3955) with
| true -> begin
tm
end
| uu____3956 -> begin
(

let uu____3957 = (FStar_Syntax_Util.head_and_args tm)
in (match (uu____3957) with
| (head1, args) -> begin
(

let uu____3983 = (

let uu____3984 = (FStar_Syntax_Util.un_uinst head1)
in uu____3984.FStar_Syntax_Syntax.n)
in (match (uu____3983) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3988 = (FStar_List.tryFind (fun ps -> (FStar_Syntax_Syntax.fv_eq_lid fv ps.name)) cfg.primitive_steps)
in (match (uu____3988) with
| FStar_Pervasives_Native.None -> begin
tm
end
| FStar_Pervasives_Native.Some (prim_step) -> begin
(match (((FStar_List.length args) < prim_step.arity)) with
| true -> begin
tm
end
| uu____3999 -> begin
(

let uu____4000 = (prim_step.interpretation head1.FStar_Syntax_Syntax.pos args)
in (match (uu____4000) with
| FStar_Pervasives_Native.None -> begin
tm
end
| FStar_Pervasives_Native.Some (reduced) -> begin
reduced
end))
end)
end))
end
| uu____4003 -> begin
tm
end))
end))
end)))


let reduce_equality : cfg  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (reduce_primops (

let uu___158_4010 = cfg
in {steps = (Primops)::[]; tcenv = uu___158_4010.tcenv; delta_level = uu___158_4010.delta_level; primitive_steps = equality_ops}) tm))


let maybe_simplify : cfg  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (

let steps = cfg.steps
in (

let w = (fun t -> (

let uu___159_4032 = t
in {FStar_Syntax_Syntax.n = uu___159_4032.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___159_4032.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___159_4032.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_Pervasives_Native.Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid) -> begin
FStar_Pervasives_Native.Some (false)
end
| uu____4051 -> begin
FStar_Pervasives_Native.None
end))
in (

let simplify = (fun arg -> (((simp_t (FStar_Pervasives_Native.fst arg))), (arg)))
in (

let uu____4078 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps))
in (match (uu____4078) with
| true -> begin
(reduce_primops cfg tm)
end
| uu____4079 -> begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____4081; FStar_Syntax_Syntax.pos = uu____4082; FStar_Syntax_Syntax.vars = uu____4083}, uu____4084); FStar_Syntax_Syntax.tk = uu____4085; FStar_Syntax_Syntax.pos = uu____4086; FStar_Syntax_Syntax.vars = uu____4087}, args) -> begin
(

let uu____4107 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____4107) with
| true -> begin
(

let uu____4108 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____4108) with
| ((FStar_Pervasives_Native.Some (true), uu____4141))::((uu____4142, (arg, uu____4144)))::[] -> begin
arg
end
| ((uu____4185, (arg, uu____4187)))::((FStar_Pervasives_Native.Some (true), uu____4188))::[] -> begin
arg
end
| ((FStar_Pervasives_Native.Some (false), uu____4229))::(uu____4230)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____4268)::((FStar_Pervasives_Native.Some (false), uu____4269))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____4307 -> begin
tm
end))
end
| uu____4316 -> begin
(

let uu____4317 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____4317) with
| true -> begin
(

let uu____4318 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____4318) with
| ((FStar_Pervasives_Native.Some (true), uu____4351))::(uu____4352)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____4390)::((FStar_Pervasives_Native.Some (true), uu____4391))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____4429))::((uu____4430, (arg, uu____4432)))::[] -> begin
arg
end
| ((uu____4473, (arg, uu____4475)))::((FStar_Pervasives_Native.Some (false), uu____4476))::[] -> begin
arg
end
| uu____4517 -> begin
tm
end))
end
| uu____4526 -> begin
(

let uu____4527 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____4527) with
| true -> begin
(

let uu____4528 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____4528) with
| (uu____4561)::((FStar_Pervasives_Native.Some (true), uu____4562))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____4600))::(uu____4601)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____4639))::((uu____4640, (arg, uu____4642)))::[] -> begin
arg
end
| uu____4683 -> begin
tm
end))
end
| uu____4692 -> begin
(

let uu____4693 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____4693) with
| true -> begin
(

let uu____4694 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____4694) with
| ((FStar_Pervasives_Native.Some (true), uu____4727))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____4751))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____4775 -> begin
tm
end))
end
| uu____4784 -> begin
(

let uu____4785 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____4785) with
| true -> begin
(match (args) with
| ((t, uu____4787))::[] -> begin
(

let uu____4800 = (

let uu____4801 = (FStar_Syntax_Subst.compress t)
in uu____4801.FStar_Syntax_Syntax.n)
in (match (uu____4800) with
| FStar_Syntax_Syntax.Tm_abs ((uu____4804)::[], body, uu____4806) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____4832 -> begin
tm
end)
end
| uu____4834 -> begin
tm
end))
end
| ((uu____4835, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4836))))::((t, uu____4838))::[] -> begin
(

let uu____4865 = (

let uu____4866 = (FStar_Syntax_Subst.compress t)
in uu____4866.FStar_Syntax_Syntax.n)
in (match (uu____4865) with
| FStar_Syntax_Syntax.Tm_abs ((uu____4869)::[], body, uu____4871) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____4897 -> begin
tm
end)
end
| uu____4899 -> begin
tm
end))
end
| uu____4900 -> begin
tm
end)
end
| uu____4906 -> begin
(

let uu____4907 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____4907) with
| true -> begin
(match (args) with
| ((t, uu____4909))::[] -> begin
(

let uu____4922 = (

let uu____4923 = (FStar_Syntax_Subst.compress t)
in uu____4923.FStar_Syntax_Syntax.n)
in (match (uu____4922) with
| FStar_Syntax_Syntax.Tm_abs ((uu____4926)::[], body, uu____4928) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____4954 -> begin
tm
end)
end
| uu____4956 -> begin
tm
end))
end
| ((uu____4957, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4958))))::((t, uu____4960))::[] -> begin
(

let uu____4987 = (

let uu____4988 = (FStar_Syntax_Subst.compress t)
in uu____4988.FStar_Syntax_Syntax.n)
in (match (uu____4987) with
| FStar_Syntax_Syntax.Tm_abs ((uu____4991)::[], body, uu____4993) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____5019 -> begin
tm
end)
end
| uu____5021 -> begin
tm
end))
end
| uu____5022 -> begin
tm
end)
end
| uu____5028 -> begin
(reduce_equality cfg tm)
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5030; FStar_Syntax_Syntax.pos = uu____5031; FStar_Syntax_Syntax.vars = uu____5032}, args) -> begin
(

let uu____5048 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____5048) with
| true -> begin
(

let uu____5049 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____5049) with
| ((FStar_Pervasives_Native.Some (true), uu____5082))::((uu____5083, (arg, uu____5085)))::[] -> begin
arg
end
| ((uu____5126, (arg, uu____5128)))::((FStar_Pervasives_Native.Some (true), uu____5129))::[] -> begin
arg
end
| ((FStar_Pervasives_Native.Some (false), uu____5170))::(uu____5171)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____5209)::((FStar_Pervasives_Native.Some (false), uu____5210))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____5248 -> begin
tm
end))
end
| uu____5257 -> begin
(

let uu____5258 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____5258) with
| true -> begin
(

let uu____5259 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____5259) with
| ((FStar_Pervasives_Native.Some (true), uu____5292))::(uu____5293)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____5331)::((FStar_Pervasives_Native.Some (true), uu____5332))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____5370))::((uu____5371, (arg, uu____5373)))::[] -> begin
arg
end
| ((uu____5414, (arg, uu____5416)))::((FStar_Pervasives_Native.Some (false), uu____5417))::[] -> begin
arg
end
| uu____5458 -> begin
tm
end))
end
| uu____5467 -> begin
(

let uu____5468 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____5468) with
| true -> begin
(

let uu____5469 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____5469) with
| (uu____5502)::((FStar_Pervasives_Native.Some (true), uu____5503))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____5541))::(uu____5542)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____5580))::((uu____5581, (arg, uu____5583)))::[] -> begin
arg
end
| uu____5624 -> begin
tm
end))
end
| uu____5633 -> begin
(

let uu____5634 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____5634) with
| true -> begin
(

let uu____5635 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____5635) with
| ((FStar_Pervasives_Native.Some (true), uu____5668))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____5692))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____5716 -> begin
tm
end))
end
| uu____5725 -> begin
(

let uu____5726 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____5726) with
| true -> begin
(match (args) with
| ((t, uu____5728))::[] -> begin
(

let uu____5741 = (

let uu____5742 = (FStar_Syntax_Subst.compress t)
in uu____5742.FStar_Syntax_Syntax.n)
in (match (uu____5741) with
| FStar_Syntax_Syntax.Tm_abs ((uu____5745)::[], body, uu____5747) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____5773 -> begin
tm
end)
end
| uu____5775 -> begin
tm
end))
end
| ((uu____5776, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____5777))))::((t, uu____5779))::[] -> begin
(

let uu____5806 = (

let uu____5807 = (FStar_Syntax_Subst.compress t)
in uu____5807.FStar_Syntax_Syntax.n)
in (match (uu____5806) with
| FStar_Syntax_Syntax.Tm_abs ((uu____5810)::[], body, uu____5812) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____5838 -> begin
tm
end)
end
| uu____5840 -> begin
tm
end))
end
| uu____5841 -> begin
tm
end)
end
| uu____5847 -> begin
(

let uu____5848 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____5848) with
| true -> begin
(match (args) with
| ((t, uu____5850))::[] -> begin
(

let uu____5863 = (

let uu____5864 = (FStar_Syntax_Subst.compress t)
in uu____5864.FStar_Syntax_Syntax.n)
in (match (uu____5863) with
| FStar_Syntax_Syntax.Tm_abs ((uu____5867)::[], body, uu____5869) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____5895 -> begin
tm
end)
end
| uu____5897 -> begin
tm
end))
end
| ((uu____5898, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____5899))))::((t, uu____5901))::[] -> begin
(

let uu____5928 = (

let uu____5929 = (FStar_Syntax_Subst.compress t)
in uu____5929.FStar_Syntax_Syntax.n)
in (match (uu____5928) with
| FStar_Syntax_Syntax.Tm_abs ((uu____5932)::[], body, uu____5934) -> begin
(match ((simp_t body)) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____5960 -> begin
tm
end)
end
| uu____5962 -> begin
tm
end))
end
| uu____5963 -> begin
tm
end)
end
| uu____5969 -> begin
(reduce_equality cfg tm)
end))
end))
end))
end))
end))
end))
end
| uu____5970 -> begin
tm
end)
end)))))))


let is_norm_request = (fun hd1 args -> (

let uu____5985 = (

let uu____5989 = (

let uu____5990 = (FStar_Syntax_Util.un_uinst hd1)
in uu____5990.FStar_Syntax_Syntax.n)
in ((uu____5989), (args)))
in (match (uu____5985) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5995)::(uu____5996)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5999)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize)
end
| uu____6001 -> begin
false
end)))


let get_norm_request = (fun args -> (match (args) with
| (uu____6020)::((tm, uu____6022))::[] -> begin
tm
end
| ((tm, uu____6032))::[] -> begin
tm
end
| uu____6037 -> begin
(failwith "Impossible")
end))


let is_reify_head : stack_elt Prims.list  ->  Prims.bool = (fun uu___135_6044 -> (match (uu___135_6044) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____6046; FStar_Syntax_Syntax.pos = uu____6047; FStar_Syntax_Syntax.vars = uu____6048}, uu____6049, uu____6050))::uu____6051 -> begin
true
end
| uu____6057 -> begin
false
end))


let is_fstar_tactics_embed : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____6062 = (

let uu____6063 = (FStar_Syntax_Util.un_uinst t)
in uu____6063.FStar_Syntax_Syntax.n)
in (match (uu____6062) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_tactics_embed_lid)
end
| uu____6067 -> begin
false
end)))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let firstn = (fun k l -> (match (((FStar_List.length l) < k)) with
| true -> begin
((l), ([]))
end
| uu____6179 -> begin
(FStar_Util.first_N k l)
end))
in ((log cfg (fun uu____6181 -> (

let uu____6182 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____6183 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6184 = (

let uu____6185 = (

let uu____6187 = (firstn (Prims.parse_int "4") stack1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6187))
in (stack_to_string uu____6185))
in (FStar_Util.print3 ">>> %s\nNorm %s with top of the stack %s \n" uu____6182 uu____6183 uu____6184))))));
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____6199) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____6220) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_constant (uu____6229) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____6230) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6231; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = uu____6232}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6237; FStar_Syntax_Syntax.fv_delta = uu____6238; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6242; FStar_Syntax_Syntax.fv_delta = uu____6243; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6244))}) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____6252; FStar_Syntax_Syntax.pos = uu____6253; FStar_Syntax_Syntax.vars = uu____6254}, uu____6255) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_tactics_embed_lid) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when (is_fstar_tactics_embed hd1) -> begin
(

let args1 = (closures_as_args_delayed cfg env args)
in (

let t2 = (

let uu___160_6295 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd1), (args1))); FStar_Syntax_Syntax.tk = uu___160_6295.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___160_6295.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___160_6295.FStar_Syntax_Syntax.vars})
in (

let t3 = (reduce_primops cfg t2)
in (rebuild cfg env stack1 t3))))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when (((

let uu____6324 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoFullNorm))
in (not (uu____6324))) && (is_norm_request hd1 args)) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid)))) -> begin
(

let tm = (get_norm_request args)
in (

let s = (Reify)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Primops)::[]
in (

let cfg' = (

let uu___161_6337 = cfg
in {steps = s; tcenv = uu___161_6337.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]; primitive_steps = uu___161_6337.primitive_steps})
in (

let stack' = (Debug (t1))::(Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (norm cfg' env stack' tm)))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____6342; FStar_Syntax_Syntax.pos = uu____6343; FStar_Syntax_Syntax.vars = uu____6344}, (a1)::(a2)::rest) -> begin
(

let uu____6378 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6378) with
| (hd1, uu____6389) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), ((a1)::[])))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (norm cfg env stack1 t2)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____6444)); FStar_Syntax_Syntax.tk = uu____6445; FStar_Syntax_Syntax.pos = uu____6446; FStar_Syntax_Syntax.vars = uu____6447}, (a)::[]) when ((FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) && (is_reify_head stack1)) -> begin
(

let uu____6470 = (FStar_List.tl stack1)
in (norm cfg env uu____6470 (FStar_Pervasives_Native.fst a)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____6473; FStar_Syntax_Syntax.pos = uu____6474; FStar_Syntax_Syntax.vars = uu____6475}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let uu____6498 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6498) with
| (reify_head, uu____6509) -> begin
(

let a1 = (

let uu____6525 = (FStar_All.pipe_left FStar_Syntax_Util.unascribe (FStar_Pervasives_Native.fst a))
in (FStar_Syntax_Subst.compress uu____6525))
in (match (a1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____6528)); FStar_Syntax_Syntax.tk = uu____6529; FStar_Syntax_Syntax.pos = uu____6530; FStar_Syntax_Syntax.vars = uu____6531}, (a2)::[]) -> begin
(norm cfg env stack1 (FStar_Pervasives_Native.fst a2))
end
| uu____6556 -> begin
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

let uu____6564 = (mk (FStar_Syntax_Syntax.Tm_type (u1)) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 uu____6564)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let uu____6571 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____6571) with
| true -> begin
(norm cfg env stack1 t')
end
| uu____6572 -> begin
(

let us1 = (

let uu____6574 = (

let uu____6578 = (FStar_List.map (norm_universe cfg env) us)
in ((uu____6578), (t1.FStar_Syntax_Syntax.pos)))
in UnivArgs (uu____6574))
in (

let stack2 = (us1)::stack1
in (norm cfg env stack2 t')))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t1
in (

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun uu___136_6587 -> (match (uu___136_6587) with
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
| uu____6589 -> begin
(

let r_env = (

let uu____6591 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv uu____6591))
in (

let uu____6592 = (FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6592) with
| FStar_Pervasives_Native.None -> begin
((log cfg (fun uu____6603 -> (FStar_Util.print "Tm_fvar case 2\n" [])));
(rebuild cfg env stack1 t1);
)
end
| FStar_Pervasives_Native.Some (us, t2) -> begin
((log cfg (fun uu____6609 -> (

let uu____6610 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6611 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____6610 uu____6611)))));
(

let t3 = (

let uu____6613 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))))
in (match (uu____6613) with
| true -> begin
t2
end
| uu____6614 -> begin
(FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) t2)
end))
in (

let n1 = (FStar_List.length us)
in (match ((n1 > (Prims.parse_int "0"))) with
| true -> begin
(match (stack1) with
| (UnivArgs (us', uu____6625))::stack2 -> begin
(

let env1 = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env1 u -> (Univ (u))::env1) env))
in (norm cfg env1 stack2 t3))
end
| uu____6638 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack1 t3)
end
| uu____6639 -> begin
(

let uu____6640 = (

let uu____6641 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" uu____6641))
in (failwith uu____6640))
end)
end
| uu____6646 -> begin
(norm cfg env stack1 t3)
end)));
)
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____6648 = (lookup_bvar env x)
in (match (uu____6648) with
| Univ (uu____6649) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env1, t0, r, fix) -> begin
(match (((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps))))) with
| true -> begin
(

let uu____6664 = (FStar_ST.read r)
in (match (uu____6664) with
| FStar_Pervasives_Native.Some (env2, t') -> begin
((log cfg (fun uu____6683 -> (

let uu____6684 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6685 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" uu____6684 uu____6685)))));
(

let uu____6686 = (

let uu____6687 = (FStar_Syntax_Subst.compress t')
in uu____6687.FStar_Syntax_Syntax.n)
in (match (uu____6686) with
| FStar_Syntax_Syntax.Tm_abs (uu____6690) -> begin
(norm cfg env2 stack1 t')
end
| uu____6705 -> begin
(rebuild cfg env2 stack1 t')
end));
)
end
| FStar_Pervasives_Native.None -> begin
(norm cfg env1 ((MemoLazy (r))::stack1) t0)
end))
end
| uu____6712 -> begin
(norm cfg env1 stack1 t0)
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack1) with
| (UnivArgs (uu____6738))::uu____6739 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (uu____6744))::uu____6745 -> begin
(failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, uu____6751, uu____6752))::stack_rest -> begin
(match (c) with
| Univ (uu____6755) -> begin
(norm cfg ((c)::env) stack_rest t1)
end
| uu____6756 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (uu____6759)::[] -> begin
(match (lopt) with
| FStar_Pervasives_Native.None when (FStar_Options.__unit_tests ()) -> begin
((log cfg (fun uu____6772 -> (

let uu____6773 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____6773))));
(norm cfg ((c)::env) stack_rest body);
)
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (l, cflags)) when (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid)) || (FStar_All.pipe_right cflags (FStar_Util.for_some (fun uu___137_6787 -> (match (uu___137_6787) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____6788 -> begin
false
end))))) -> begin
((log cfg (fun uu____6790 -> (

let uu____6791 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____6791))));
(norm cfg ((c)::env) stack_rest body);
)
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
((log cfg (fun uu____6802 -> (

let uu____6803 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____6803))));
(norm cfg ((c)::env) stack_rest body);
)
end
| uu____6804 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| uu____6811 -> begin
(

let cfg1 = (

let uu___162_6819 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = uu___162_6819.tcenv; delta_level = uu___162_6819.delta_level; primitive_steps = uu___162_6819.primitive_steps})
in (

let uu____6820 = (closure_as_term cfg1 env t1)
in (rebuild cfg1 env stack1 uu____6820)))
end)
end
| (uu____6821)::tl1 -> begin
((log cfg (fun uu____6831 -> (

let uu____6832 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____6832))));
(

let body1 = (mk (FStar_Syntax_Syntax.Tm_abs (((tl1), (body), (lopt)))) t1.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body1));
)
end)
end)
end
| (Steps (s, ps, dl))::stack2 -> begin
(norm (

let uu___163_6856 = cfg
in {steps = s; tcenv = uu___163_6856.tcenv; delta_level = dl; primitive_steps = ps}) env stack2 t1)
end
| (MemoLazy (r))::stack2 -> begin
((set_memo r ((env), (t1)));
(log cfg (fun uu____6869 -> (

let uu____6870 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____6870))));
(norm cfg env stack2 t1);
)
end
| (Debug (uu____6871))::uu____6872 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____6874 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____6874))
end
| uu____6875 -> begin
(

let uu____6876 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____6876) with
| (bs1, body1, opening) -> begin
(

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) -> begin
(

let uu____6905 = (

let uu____6911 = (

let uu____6912 = (

let uu____6913 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____6913))
in (FStar_All.pipe_right uu____6912 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____6911 (fun _0_31 -> FStar_Util.Inl (_0_31))))
in (FStar_All.pipe_right uu____6905 (fun _0_32 -> FStar_Pervasives_Native.Some (_0_32))))
end
| uu____6938 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____6952 -> (Dummy)::env1) env))
in ((log cfg (fun uu____6957 -> (

let uu____6958 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____6958))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___164_6968 = cfg
in (

let uu____6969 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___164_6968.steps; tcenv = uu___164_6968.tcenv; delta_level = uu___164_6968.delta_level; primitive_steps = uu____6969}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Meta (uu____6979))::uu____6980 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____6984 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____6984))
end
| uu____6985 -> begin
(

let uu____6986 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____6986) with
| (bs1, body1, opening) -> begin
(

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) -> begin
(

let uu____7015 = (

let uu____7021 = (

let uu____7022 = (

let uu____7023 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____7023))
in (FStar_All.pipe_right uu____7022 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____7021 (fun _0_33 -> FStar_Util.Inl (_0_33))))
in (FStar_All.pipe_right uu____7015 (fun _0_34 -> FStar_Pervasives_Native.Some (_0_34))))
end
| uu____7048 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7062 -> (Dummy)::env1) env))
in ((log cfg (fun uu____7067 -> (

let uu____7068 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7068))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___164_7078 = cfg
in (

let uu____7079 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___164_7078.steps; tcenv = uu___164_7078.tcenv; delta_level = uu___164_7078.delta_level; primitive_steps = uu____7079}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Let (uu____7089))::uu____7090 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7096 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7096))
end
| uu____7097 -> begin
(

let uu____7098 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7098) with
| (bs1, body1, opening) -> begin
(

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) -> begin
(

let uu____7127 = (

let uu____7133 = (

let uu____7134 = (

let uu____7135 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____7135))
in (FStar_All.pipe_right uu____7134 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____7133 (fun _0_35 -> FStar_Util.Inl (_0_35))))
in (FStar_All.pipe_right uu____7127 (fun _0_36 -> FStar_Pervasives_Native.Some (_0_36))))
end
| uu____7160 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7174 -> (Dummy)::env1) env))
in ((log cfg (fun uu____7179 -> (

let uu____7180 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7180))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___164_7190 = cfg
in (

let uu____7191 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___164_7190.steps; tcenv = uu___164_7190.tcenv; delta_level = uu___164_7190.delta_level; primitive_steps = uu____7191}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (App (uu____7201))::uu____7202 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7207 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7207))
end
| uu____7208 -> begin
(

let uu____7209 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7209) with
| (bs1, body1, opening) -> begin
(

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) -> begin
(

let uu____7238 = (

let uu____7244 = (

let uu____7245 = (

let uu____7246 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____7246))
in (FStar_All.pipe_right uu____7245 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____7244 (fun _0_37 -> FStar_Util.Inl (_0_37))))
in (FStar_All.pipe_right uu____7238 (fun _0_38 -> FStar_Pervasives_Native.Some (_0_38))))
end
| uu____7271 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7285 -> (Dummy)::env1) env))
in ((log cfg (fun uu____7290 -> (

let uu____7291 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7291))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___164_7301 = cfg
in (

let uu____7302 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___164_7301.steps; tcenv = uu___164_7301.tcenv; delta_level = uu___164_7301.delta_level; primitive_steps = uu____7302}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| (Abs (uu____7312))::uu____7313 -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7323 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7323))
end
| uu____7324 -> begin
(

let uu____7325 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7325) with
| (bs1, body1, opening) -> begin
(

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) -> begin
(

let uu____7354 = (

let uu____7360 = (

let uu____7361 = (

let uu____7362 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____7362))
in (FStar_All.pipe_right uu____7361 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____7360 (fun _0_39 -> FStar_Util.Inl (_0_39))))
in (FStar_All.pipe_right uu____7354 (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40))))
end
| uu____7387 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7401 -> (Dummy)::env1) env))
in ((log cfg (fun uu____7406 -> (

let uu____7407 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7407))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___164_7417 = cfg
in (

let uu____7418 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___164_7417.steps; tcenv = uu___164_7417.tcenv; delta_level = uu___164_7417.delta_level; primitive_steps = uu____7418}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end
| [] -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7428 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7428))
end
| uu____7429 -> begin
(

let uu____7430 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7430) with
| (bs1, body1, opening) -> begin
(

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) -> begin
(

let uu____7459 = (

let uu____7465 = (

let uu____7466 = (

let uu____7467 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____7467))
in (FStar_All.pipe_right uu____7466 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____7465 (fun _0_41 -> FStar_Util.Inl (_0_41))))
in (FStar_All.pipe_right uu____7459 (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42))))
end
| uu____7492 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7506 -> (Dummy)::env1) env))
in ((log cfg (fun uu____7511 -> (

let uu____7512 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____7512))));
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___164_7522 = cfg
in (

let uu____7523 = (FStar_List.filter (fun ps -> ps.strong_reduction_ok) cfg.primitive_steps)
in {steps = uu___164_7522.steps; tcenv = uu___164_7522.tcenv; delta_level = uu___164_7522.delta_level; primitive_steps = uu____7523}))
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack2) body1)));
)))
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack2 = (FStar_All.pipe_right stack1 (FStar_List.fold_right (fun uu____7555 stack2 -> (match (uu____7555) with
| (a, aq) -> begin
(

let uu____7563 = (

let uu____7564 = (

let uu____7568 = (

let uu____7569 = (

let uu____7579 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____7579), (false)))
in Clos (uu____7569))
in ((uu____7568), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____7564))
in (uu____7563)::stack2)
end)) args))
in ((log cfg (fun uu____7601 -> (

let uu____7602 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____7602))));
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

let uu___165_7623 = x
in {FStar_Syntax_Syntax.ppname = uu___165_7623.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___165_7623.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 t2)))
end
| uu____7624 -> begin
(

let uu____7627 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7627))
end)
end
| uu____7628 -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let uu____7630 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____7630) with
| (closing, f1) -> begin
(

let f2 = (norm cfg ((Dummy)::env) [] f1)
in (

let t2 = (

let uu____7646 = (

let uu____7647 = (

let uu____7652 = (FStar_Syntax_Subst.close closing f2)
in (((

let uu___166_7653 = x
in {FStar_Syntax_Syntax.ppname = uu___166_7653.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___166_7653.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (uu____7652)))
in FStar_Syntax_Syntax.Tm_refine (uu____7647))
in (mk uu____7646 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack1 t2)))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____7666 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7666))
end
| uu____7667 -> begin
(

let uu____7668 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7668) with
| (bs1, c1) -> begin
(

let c2 = (

let uu____7674 = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____7680 -> (Dummy)::env1) env))
in (norm_comp cfg uu____7674 c1))
in (

let t2 = (

let uu____7687 = (norm_binders cfg env bs1)
in (FStar_Syntax_Util.arrow uu____7687 c2))
in (rebuild cfg env stack1 t2)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) -> begin
(match (stack1) with
| (Match (uu____7730))::uu____7731 -> begin
(norm cfg env stack1 t11)
end
| (Arg (uu____7736))::uu____7737 -> begin
(norm cfg env stack1 t11)
end
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____7742; FStar_Syntax_Syntax.pos = uu____7743; FStar_Syntax_Syntax.vars = uu____7744}, uu____7745, uu____7746))::uu____7747 -> begin
(norm cfg env stack1 t11)
end
| (MemoLazy (uu____7753))::uu____7754 -> begin
(norm cfg env stack1 t11)
end
| uu____7759 -> begin
(

let t12 = (norm cfg env [] t11)
in ((log cfg (fun uu____7762 -> (FStar_Util.print_string "+++ Normalizing ascription \n")));
(

let tc1 = (match (tc) with
| FStar_Util.Inl (t2) -> begin
(

let uu____7775 = (norm cfg env [] t2)
in FStar_Util.Inl (uu____7775))
end
| FStar_Util.Inr (c) -> begin
(

let uu____7783 = (norm_comp cfg env c)
in FStar_Util.Inr (uu____7783))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (norm cfg env []))
in (

let uu____7788 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t12), (((tc1), (tacopt1))), (l)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack1 uu____7788))));
))
end)
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let stack2 = (Match (((env), (branches), (t1.FStar_Syntax_Syntax.pos))))::stack1
in (norm cfg env stack2 head1))
end
| FStar_Syntax_Syntax.Tm_let ((uu____7839, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____7840); FStar_Syntax_Syntax.lbunivs = uu____7841; FStar_Syntax_Syntax.lbtyp = uu____7842; FStar_Syntax_Syntax.lbeff = uu____7843; FStar_Syntax_Syntax.lbdef = uu____7844})::uu____7845), uu____7846) -> begin
(rebuild cfg env stack1 t1)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n1 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in (

let uu____7872 = ((

let uu____7873 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps))
in (not (uu____7873))) && ((FStar_Syntax_Util.is_pure_effect n1) || ((FStar_Syntax_Util.is_ghost_effect n1) && (

let uu____7874 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (not (uu____7874))))))
in (match (uu____7872) with
| true -> begin
(

let env1 = (

let uu____7877 = (

let uu____7878 = (

let uu____7888 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (uu____7888), (false)))
in Clos (uu____7878))
in (uu____7877)::env)
in (norm cfg env1 stack1 body))
end
| uu____7911 -> begin
(

let uu____7912 = (

let uu____7915 = (

let uu____7916 = (

let uu____7917 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right uu____7917 FStar_Syntax_Syntax.mk_binder))
in (uu____7916)::[])
in (FStar_Syntax_Subst.open_term uu____7915 body))
in (match (uu____7912) with
| (bs, body1) -> begin
(

let lb1 = (

let uu___167_7923 = lb
in (

let uu____7924 = (

let uu____7927 = (

let uu____7928 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____7928 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7927 (fun _0_43 -> FStar_Util.Inl (_0_43))))
in (

let uu____7937 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____7940 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu____7924; FStar_Syntax_Syntax.lbunivs = uu___167_7923.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____7937; FStar_Syntax_Syntax.lbeff = uu___167_7923.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____7940}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env1 uu____7950 -> (Dummy)::env1) env))
in (norm cfg env' ((Let (((env), (bs), (lb1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(

let uu____7966 = (closure_as_term cfg env t1)
in (rebuild cfg env stack1 uu____7966))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let uu____7979 = (FStar_List.fold_right (fun lb uu____8001 -> (match (uu____8001) with
| (rec_env, memos, i) -> begin
(

let f_i = (

let uu____8040 = (

let uu___168_8041 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___168_8041.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___168_8041.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm uu____8040))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t1.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let rec_env1 = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env1), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (FStar_Pervasives_Native.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (uu____7979) with
| (rec_env, memos, uu____8101) -> begin
(

let uu____8116 = (FStar_List.map2 (fun lb memo -> (FStar_ST.write memo (FStar_Pervasives_Native.Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (FStar_Pervasives_Native.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env1 -> (

let uu____8158 = (

let uu____8159 = (

let uu____8169 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (uu____8169), (false)))
in Clos (uu____8159))
in (uu____8158)::env1)) (FStar_Pervasives_Native.snd lbs) env)
in (norm cfg body_env stack1 body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head1, m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m1, t2) -> begin
(

let should_reify = (match (stack1) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____8207; FStar_Syntax_Syntax.pos = uu____8208; FStar_Syntax_Syntax.vars = uu____8209}, uu____8210, uu____8211))::uu____8212 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____8218 -> begin
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

let uu____8225 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____8225) with
| true -> begin
(

let uu___169_8226 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::(NoDeltaSteps)::[]; tcenv = uu___169_8226.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___169_8226.primitive_steps})
end
| uu____8227 -> begin
(

let uu___170_8228 = cfg
in {steps = (FStar_List.append ((NoDeltaSteps)::(Exclude (Zeta))::[]) cfg.steps); tcenv = uu___170_8228.tcenv; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___170_8228.primitive_steps})
end))
in (norm cfg1 env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m1), (t3)))), (t3.FStar_Syntax_Syntax.pos))))::stack2) head1))))
end
| uu____8229 -> begin
(

let uu____8230 = (

let uu____8231 = (FStar_Syntax_Subst.compress head1)
in uu____8231.FStar_Syntax_Syntax.n)
in (match (uu____8230) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m1)
in (

let uu____8245 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____8245) with
| (uu____8246, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____8250) -> begin
(failwith "Cannot reify a top-level let binding")
end
| FStar_Util.Inl (x) -> begin
(

let is_return = (fun e -> (

let uu____8257 = (

let uu____8258 = (FStar_Syntax_Subst.compress e)
in uu____8258.FStar_Syntax_Syntax.n)
in (match (uu____8257) with
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____8263, uu____8264)) -> begin
(

let uu____8273 = (

let uu____8274 = (FStar_Syntax_Subst.compress e1)
in uu____8274.FStar_Syntax_Syntax.n)
in (match (uu____8273) with
| FStar_Syntax_Syntax.Tm_meta (e2, FStar_Syntax_Syntax.Meta_monadic_lift (uu____8279, msrc, uu____8281)) when (FStar_Syntax_Util.is_pure_effect msrc) -> begin
(

let uu____8290 = (FStar_Syntax_Subst.compress e2)
in FStar_Pervasives_Native.Some (uu____8290))
end
| uu____8291 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____8292 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____8293 = (is_return lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____8293) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let lb1 = (

let uu___171_8297 = lb
in {FStar_Syntax_Syntax.lbname = uu___171_8297.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___171_8297.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___171_8297.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = e})
in (

let uu____8298 = (FStar_List.tl stack1)
in (

let uu____8299 = (

let uu____8300 = (

let uu____8303 = (

let uu____8304 = (

let uu____8312 = (FStar_Syntax_Util.mk_reify body)
in ((((false), ((lb1)::[]))), (uu____8312)))
in FStar_Syntax_Syntax.Tm_let (uu____8304))
in (FStar_Syntax_Syntax.mk uu____8303))
in (uu____8300 FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos))
in (norm cfg env uu____8298 uu____8299))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8329 = (

let uu____8330 = (is_return body)
in (match (uu____8330) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_bvar (y); FStar_Syntax_Syntax.tk = uu____8333; FStar_Syntax_Syntax.pos = uu____8334; FStar_Syntax_Syntax.vars = uu____8335}) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____8340 -> begin
false
end))
in (match (uu____8329) with
| true -> begin
(norm cfg env stack1 lb.FStar_Syntax_Syntax.lbdef)
end
| uu____8342 -> begin
(

let head2 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body1 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify body)
in (

let body2 = (

let uu____8360 = (

let uu____8363 = (

let uu____8364 = (

let uu____8379 = (

let uu____8381 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____8381)::[])
in ((uu____8379), (body1), (FStar_Pervasives_Native.Some (FStar_Util.Inr (((m1), ([])))))))
in FStar_Syntax_Syntax.Tm_abs (uu____8364))
in (FStar_Syntax_Syntax.mk uu____8363))
in (uu____8360 FStar_Pervasives_Native.None body1.FStar_Syntax_Syntax.pos))
in (

let close1 = (closure_as_term cfg env)
in (

let bind_inst = (

let uu____8414 = (

let uu____8415 = (FStar_Syntax_Subst.compress bind_repr)
in uu____8415.FStar_Syntax_Syntax.n)
in (match (uu____8414) with
| FStar_Syntax_Syntax.Tm_uinst (bind1, (uu____8421)::(uu____8422)::[]) -> begin
(

let uu____8428 = (

let uu____8431 = (

let uu____8432 = (

let uu____8437 = (

let uu____8439 = (

let uu____8440 = (close1 lb.FStar_Syntax_Syntax.lbtyp)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____8440))
in (

let uu____8441 = (

let uu____8443 = (

let uu____8444 = (close1 t2)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____8444))
in (uu____8443)::[])
in (uu____8439)::uu____8441))
in ((bind1), (uu____8437)))
in FStar_Syntax_Syntax.Tm_uinst (uu____8432))
in (FStar_Syntax_Syntax.mk uu____8431))
in (uu____8428 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
end
| uu____8456 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let reified = (

let uu____8462 = (

let uu____8465 = (

let uu____8466 = (

let uu____8476 = (

let uu____8478 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____8479 = (

let uu____8481 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____8482 = (

let uu____8484 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____8485 = (

let uu____8487 = (FStar_Syntax_Syntax.as_arg head2)
in (

let uu____8488 = (

let uu____8490 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____8491 = (

let uu____8493 = (FStar_Syntax_Syntax.as_arg body2)
in (uu____8493)::[])
in (uu____8490)::uu____8491))
in (uu____8487)::uu____8488))
in (uu____8484)::uu____8485))
in (uu____8481)::uu____8482))
in (uu____8478)::uu____8479))
in ((bind_inst), (uu____8476)))
in FStar_Syntax_Syntax.Tm_app (uu____8466))
in (FStar_Syntax_Syntax.mk uu____8465))
in (uu____8462 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (

let uu____8505 = (FStar_List.tl stack1)
in (norm cfg env uu____8505 reified))))))))
end))
end)))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head_app, args) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m1)
in (

let uu____8523 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____8523) with
| (uu____8524, bind_repr) -> begin
(

let maybe_unfold_action = (fun head2 -> (

let maybe_extract_fv = (fun t3 -> (

let t4 = (

let uu____8547 = (

let uu____8548 = (FStar_Syntax_Subst.compress t3)
in uu____8548.FStar_Syntax_Syntax.n)
in (match (uu____8547) with
| FStar_Syntax_Syntax.Tm_uinst (t4, uu____8554) -> begin
t4
end
| uu____8559 -> begin
head2
end))
in (

let uu____8560 = (

let uu____8561 = (FStar_Syntax_Subst.compress t4)
in uu____8561.FStar_Syntax_Syntax.n)
in (match (uu____8560) with
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____8566 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____8567 = (maybe_extract_fv head2)
in (match (uu____8567) with
| FStar_Pervasives_Native.Some (x) when (

let uu____8573 = (FStar_Syntax_Syntax.lid_of_fv x)
in (FStar_TypeChecker_Env.is_action cfg.tcenv uu____8573)) -> begin
(

let head3 = (norm cfg env [] head2)
in (

let action_unfolded = (

let uu____8577 = (maybe_extract_fv head3)
in (match (uu____8577) with
| FStar_Pervasives_Native.Some (uu____8580) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____8581 -> begin
FStar_Pervasives_Native.Some (false)
end))
in ((head3), (action_unfolded))))
end
| uu____8584 -> begin
((head2), (FStar_Pervasives_Native.None))
end))))
in ((

let is_arg_impure = (fun uu____8595 -> (match (uu____8595) with
| (e, q) -> begin
(

let uu____8600 = (

let uu____8601 = (FStar_Syntax_Subst.compress e)
in uu____8601.FStar_Syntax_Syntax.n)
in (match (uu____8600) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m11, m2, t')) -> begin
(not ((FStar_Syntax_Util.is_pure_effect m11)))
end
| uu____8616 -> begin
false
end))
end))
in (

let uu____8617 = (

let uu____8618 = (

let uu____8622 = (FStar_Syntax_Syntax.as_arg head_app)
in (uu____8622)::args)
in (FStar_Util.for_some is_arg_impure uu____8618))
in (match (uu____8617) with
| true -> begin
(

let uu____8625 = (

let uu____8626 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format1 "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n" uu____8626))
in (failwith uu____8625))
end
| uu____8627 -> begin
()
end)));
(

let uu____8628 = (maybe_unfold_action head_app)
in (match (uu____8628) with
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

let uu____8663 = (FStar_List.tl stack1)
in (norm cfg env uu____8663 body1)))))
end));
))
end)))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (

let uu____8677 = (closure_as_term cfg env t')
in (reify_lift cfg.tcenv e msrc mtgt uu____8677))
in (

let uu____8678 = (FStar_List.tl stack1)
in (norm cfg env uu____8678 lifted)))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____8761 -> (match (uu____8761) with
| (pat, wopt, tm) -> begin
(

let uu____8799 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____8799)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches1)))) t2.FStar_Syntax_Syntax.pos)
in (

let uu____8825 = (FStar_List.tl stack1)
in (norm cfg env uu____8825 tm))))
end
| uu____8826 -> begin
(norm cfg env stack1 head1)
end))
end))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) -> begin
(

let should_reify = (match (stack1) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____8835; FStar_Syntax_Syntax.pos = uu____8836; FStar_Syntax_Syntax.vars = uu____8837}, uu____8838, uu____8839))::uu____8840 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____8846 -> begin
false
end)
in (match (should_reify) with
| true -> begin
(

let uu____8847 = (FStar_List.tl stack1)
in (

let uu____8848 = (

let uu____8849 = (closure_as_term cfg env t2)
in (reify_lift cfg.tcenv head1 m1 m' uu____8849))
in (norm cfg env uu____8847 uu____8848)))
end
| uu____8850 -> begin
(

let t3 = (norm cfg env [] t2)
in (

let uu____8852 = (((FStar_Syntax_Util.is_pure_effect m1) || (FStar_Syntax_Util.is_ghost_effect m1)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)))
in (match (uu____8852) with
| true -> begin
(

let stack2 = (Steps (((cfg.steps), (cfg.primitive_steps), (cfg.delta_level))))::stack1
in (

let cfg1 = (

let uu___172_8858 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = uu___172_8858.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___172_8858.primitive_steps})
in (norm cfg1 env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t3)))), (head1.FStar_Syntax_Syntax.pos))))::stack2) head1)))
end
| uu____8859 -> begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t3)))), (head1.FStar_Syntax_Syntax.pos))))::stack1) head1)
end)))
end))
end
| uu____8860 -> begin
(match (stack1) with
| (uu____8861)::uu____8862 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____8866) -> begin
(norm cfg env ((Meta (((m), (r))))::stack1) head1)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args1 = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args1)), (t1.FStar_Syntax_Syntax.pos))))::stack1) head1))
end
| uu____8881 -> begin
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

let uu____8891 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (uu____8891))
end
| uu____8898 -> begin
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

let uu____8910 = ed.FStar_Syntax_Syntax.return_repr
in (match (uu____8910) with
| (uu____8911, return_repr) -> begin
(

let return_inst = (

let uu____8918 = (

let uu____8919 = (FStar_Syntax_Subst.compress return_repr)
in uu____8919.FStar_Syntax_Syntax.n)
in (match (uu____8918) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (uu____8925)::[]) -> begin
(

let uu____8931 = (

let uu____8934 = (

let uu____8935 = (

let uu____8940 = (

let uu____8942 = (env.FStar_TypeChecker_Env.universe_of env t)
in (uu____8942)::[])
in ((return_tm), (uu____8940)))
in FStar_Syntax_Syntax.Tm_uinst (uu____8935))
in (FStar_Syntax_Syntax.mk uu____8934))
in (uu____8931 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end
| uu____8954 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let uu____8957 = (

let uu____8960 = (

let uu____8961 = (

let uu____8971 = (

let uu____8973 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____8974 = (

let uu____8976 = (FStar_Syntax_Syntax.as_arg e)
in (uu____8976)::[])
in (uu____8973)::uu____8974))
in ((return_inst), (uu____8971)))
in FStar_Syntax_Syntax.Tm_app (uu____8961))
in (FStar_Syntax_Syntax.mk uu____8960))
in (uu____8957 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end)))
end
| uu____8988 -> begin
(

let uu____8989 = (FStar_TypeChecker_Env.monad_leq env msrc mtgt)
in (match (uu____8989) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8991 = (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" (FStar_Ident.text_of_lid msrc) (FStar_Ident.text_of_lid mtgt))
in (failwith uu____8991))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____8992; FStar_TypeChecker_Env.mtarget = uu____8993; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____8994; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(failwith "Impossible : trying to reify a non-reifiable lift (from %s to %s)")
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____9005; FStar_TypeChecker_Env.mtarget = uu____9006; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____9007; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let uu____9025 = (FStar_Syntax_Util.mk_reify e)
in (lift t FStar_Syntax_Syntax.tun uu____9025))
end))
end))
and norm_pattern_args : cfg  ->  env  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun uu____9055 -> (match (uu____9055) with
| (a, imp) -> begin
(

let uu____9062 = (norm cfg env [] a)
in ((uu____9062), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp1 = (ghost_to_pure_aux cfg env comp)
in (match (comp1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu___173_9077 = comp1
in (

let uu____9080 = (

let uu____9081 = (

let uu____9087 = (norm cfg env [] t)
in (

let uu____9088 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____9087), (uu____9088))))
in FStar_Syntax_Syntax.Total (uu____9081))
in {FStar_Syntax_Syntax.n = uu____9080; FStar_Syntax_Syntax.tk = uu___173_9077.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___173_9077.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___173_9077.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu___174_9103 = comp1
in (

let uu____9106 = (

let uu____9107 = (

let uu____9113 = (norm cfg env [] t)
in (

let uu____9114 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____9113), (uu____9114))))
in FStar_Syntax_Syntax.GTotal (uu____9107))
in {FStar_Syntax_Syntax.n = uu____9106; FStar_Syntax_Syntax.tk = uu___174_9103.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___174_9103.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___174_9103.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____9145 -> (match (uu____9145) with
| (a, i) -> begin
(

let uu____9152 = (norm cfg env [] a)
in ((uu____9152), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___138_9157 -> (match (uu___138_9157) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____9161 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____9161))
end
| f -> begin
f
end))))
in (

let uu___175_9165 = comp1
in (

let uu____9168 = (

let uu____9169 = (

let uu___176_9170 = ct
in (

let uu____9171 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (

let uu____9172 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____9175 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = uu____9171; FStar_Syntax_Syntax.effect_name = uu___176_9170.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____9172; FStar_Syntax_Syntax.effect_args = uu____9175; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (uu____9169))
in {FStar_Syntax_Syntax.n = uu____9168; FStar_Syntax_Syntax.tk = uu___175_9165.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___175_9165.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___175_9165.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm1 = (fun t -> (norm (

let uu___177_9192 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = uu___177_9192.tcenv; delta_level = uu___177_9192.delta_level; primitive_steps = uu___177_9192.primitive_steps}) env [] t))
in (

let non_info = (fun t -> (

let uu____9197 = (norm1 t)
in (FStar_Syntax_Util.non_informative uu____9197)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____9200) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let uu___178_9214 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = uu___178_9214.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___178_9214.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___178_9214.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____9224 = ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ))
in (match (uu____9224) with
| true -> begin
(

let ct1 = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let uu___179_9229 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___179_9229.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = uu___179_9229.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___179_9229.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___179_9229.FStar_Syntax_Syntax.flags})
end
| FStar_Pervasives_Native.None -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c)
in (

let uu___180_9231 = ct1
in {FStar_Syntax_Syntax.comp_univs = uu___180_9231.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu___180_9231.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___180_9231.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___180_9231.FStar_Syntax_Syntax.flags}))
end)
in (

let uu___181_9232 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.tk = uu___181_9232.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___181_9232.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___181_9232.FStar_Syntax_Syntax.vars}))
end
| uu____9237 -> begin
c
end)))
end
| uu____9238 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env uu____9241 -> (match (uu____9241) with
| (x, imp) -> begin
(

let uu____9244 = (

let uu___182_9245 = x
in (

let uu____9246 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___182_9245.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___182_9245.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____9246}))
in ((uu____9244), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let uu____9252 = (FStar_List.fold_left (fun uu____9259 b -> (match (uu____9259) with
| (nbs', env1) -> begin
(

let b1 = (norm_binder cfg env1 b)
in (((b1)::nbs'), ((Dummy)::env1)))
end)) (([]), (env)) bs)
in (match (uu____9252) with
| (nbs, uu____9276) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) -> begin
(

let flags = (filter_out_lcomp_cflags lc)
in (

let uu____9293 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____9293) with
| true -> begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____9298 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____9298) with
| true -> begin
(

let uu____9302 = (

let uu____9305 = (

let uu____9306 = (

let uu____9309 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.comp_set_flags uu____9309 flags))
in (FStar_Syntax_Util.lcomp_of_comp uu____9306))
in FStar_Util.Inl (uu____9305))
in FStar_Pervasives_Native.Some (uu____9302))
end
| uu____9312 -> begin
(

let uu____9313 = (

let uu____9316 = (

let uu____9317 = (

let uu____9320 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.comp_set_flags uu____9320 flags))
in (FStar_Syntax_Util.lcomp_of_comp uu____9317))
in FStar_Util.Inl (uu____9316))
in FStar_Pervasives_Native.Some (uu____9313))
end)))
end
| uu____9323 -> begin
FStar_Pervasives_Native.Some (FStar_Util.Inr (((lc.FStar_Syntax_Syntax.eff_name), (flags))))
end)))
end
| uu____9333 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack1 t -> (match (stack1) with
| [] -> begin
t
end
| (Debug (tm))::stack2 -> begin
((

let uu____9345 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms")))
in (match (uu____9345) with
| true -> begin
(

let uu____9346 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____9347 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Normalized %s to %s\n" uu____9346 uu____9347)))
end
| uu____9348 -> begin
()
end));
(rebuild cfg env stack2 t);
)
end
| (Steps (s, ps, dl))::stack2 -> begin
(rebuild (

let uu___183_9358 = cfg
in {steps = s; tcenv = uu___183_9358.tcenv; delta_level = dl; primitive_steps = ps}) env stack2 t)
end
| (Meta (m, r))::stack2 -> begin
(

let t1 = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack2 t1))
end
| (MemoLazy (r))::stack2 -> begin
((set_memo r ((env), (t)));
(log cfg (fun uu____9378 -> (

let uu____9379 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" uu____9379))));
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

let uu____9416 = (

let uu___184_9417 = (FStar_Syntax_Util.abs bs1 t lopt1)
in {FStar_Syntax_Syntax.n = uu___184_9417.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___184_9417.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___184_9417.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack2 uu____9416))))
end
| (Arg (Univ (uu____9422), uu____9423, uu____9424))::uu____9425 -> begin
(failwith "Impossible")
end
| (Arg (Dummy, uu____9427, uu____9428))::uu____9429 -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack2 -> begin
(

let t1 = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack2 t1))
end
| (Arg (Clos (env1, tm, m, uu____9441), aq, r))::stack2 -> begin
((log cfg (fun uu____9457 -> (

let uu____9458 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" uu____9458))));
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
| uu____9465 -> begin
(

let stack3 = (App (((t), (aq), (r))))::stack2
in (norm cfg env1 stack3 tm))
end)
end
| uu____9468 -> begin
(

let uu____9469 = (FStar_ST.read m)
in (match (uu____9469) with
| FStar_Pervasives_Native.None -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let arg = (closure_as_term cfg env1 tm)
in (

let t1 = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack2 t1)))
end
| uu____9489 -> begin
(

let stack3 = (MemoLazy (m))::(App (((t), (aq), (r))))::stack2
in (norm cfg env1 stack3 tm))
end)
end
| FStar_Pervasives_Native.Some (uu____9495, a) -> begin
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

let uu____9517 = (maybe_simplify cfg t1)
in (rebuild cfg env stack2 uu____9517)))
end
| (Match (env1, branches, r))::stack2 -> begin
((log cfg (fun uu____9524 -> (

let uu____9525 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" uu____9525))));
(

let scrutinee = t
in (

let norm_and_rebuild_match = (fun uu____9530 -> ((log cfg (fun uu____9532 -> (

let uu____9533 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____9534 = (

let uu____9535 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____9542 -> (match (uu____9542) with
| (p, uu____9548, uu____9549) -> begin
(FStar_Syntax_Print.pat_to_string p)
end))))
in (FStar_All.pipe_right uu____9535 (FStar_String.concat "\n\t")))
in (FStar_Util.print2 "match is irreducible: scrutinee=%s\nbranches=%s\n" uu____9533 uu____9534)))));
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg_exclude_iota_zeta = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun uu___139_9559 -> (match (uu___139_9559) with
| FStar_TypeChecker_Env.Inlining -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| uu____9560 -> begin
false
end))))
in (

let steps' = (

let uu____9563 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____9563) with
| true -> begin
(Exclude (Zeta))::[]
end
| uu____9565 -> begin
(Exclude (Iota))::(Exclude (Zeta))::[]
end))
in (

let uu___185_9566 = cfg
in {steps = (FStar_List.append steps' cfg.steps); tcenv = uu___185_9566.tcenv; delta_level = new_delta; primitive_steps = uu___185_9566.primitive_steps})))
in (

let norm_or_whnf = (fun env2 t1 -> (match (whnf) with
| true -> begin
(closure_as_term cfg_exclude_iota_zeta env2 t1)
end
| uu____9576 -> begin
(norm cfg_exclude_iota_zeta env2 [] t1)
end))
in (

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____9600) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____9616 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____9650 uu____9651 -> (match (((uu____9650), (uu____9651))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____9716 = (norm_pat env3 p1)
in (match (uu____9716) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____9616) with
| (pats1, env3) -> begin
(((

let uu___186_9782 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.ty = uu___186_9782.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___186_9782.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___187_9796 = x
in (

let uu____9797 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___187_9796.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___187_9796.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____9797}))
in (((

let uu___188_9803 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.ty = uu___188_9803.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___188_9803.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___189_9808 = x
in (

let uu____9809 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___189_9808.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___189_9808.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____9809}))
in (((

let uu___190_9815 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.ty = uu___190_9815.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___190_9815.FStar_Syntax_Syntax.p})), ((Dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t1) -> begin
(

let x1 = (

let uu___191_9825 = x
in (

let uu____9826 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___191_9825.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___191_9825.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____9826}))
in (

let t2 = (norm_or_whnf env2 t1)
in (((

let uu___192_9833 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t2))); FStar_Syntax_Syntax.ty = uu___192_9833.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___192_9833.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let branches1 = (match (env1) with
| [] when whnf -> begin
branches
end
| uu____9837 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch1 -> (

let uu____9840 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____9840) with
| (p, wopt, e) -> begin
(

let uu____9858 = (norm_pat env1 p)
in (match (uu____9858) with
| (p1, env2) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____9882 = (norm_or_whnf env2 w)
in FStar_Pervasives_Native.Some (uu____9882))
end)
in (

let e1 = (norm_or_whnf env2 e)
in (FStar_Syntax_Util.branch ((p1), (wopt1), (e1)))))
end))
end)))))
end)
in (

let uu____9887 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches1)))) r)
in (rebuild cfg env1 stack2 uu____9887)))))));
))
in (

let rec is_cons = (fun head1 -> (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, uu____9897) -> begin
(is_cons h)
end
| FStar_Syntax_Syntax.Tm_constant (uu____9902) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____9903; FStar_Syntax_Syntax.fv_delta = uu____9904; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____9908; FStar_Syntax_Syntax.fv_delta = uu____9909; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____9910))}) -> begin
true
end
| uu____9917 -> begin
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

let uu____10016 = (FStar_Syntax_Util.head_and_args scrutinee2)
in (match (uu____10016) with
| (head1, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____10048) -> begin
FStar_Util.Inl ((scrutinee2)::[])
end
| FStar_Syntax_Syntax.Pat_wild (uu____10050) -> begin
FStar_Util.Inl ((scrutinee2)::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____10052) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| uu____10064 -> begin
(

let uu____10065 = (

let uu____10066 = (is_cons head1)
in (not (uu____10066)))
in FStar_Util.Inr (uu____10065))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let uu____10080 = (

let uu____10081 = (FStar_Syntax_Util.un_uinst head1)
in uu____10081.FStar_Syntax_Syntax.n)
in (match (uu____10080) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| uu____10088 -> begin
(

let uu____10089 = (

let uu____10090 = (is_cons head1)
in (not (uu____10090)))
in FStar_Util.Inr (uu____10089))
end))
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t1, uu____10124))::rest_a, ((p1, uu____10127))::rest_p) -> begin
(

let uu____10155 = (matches_pat t1 p1)
in (match (uu____10155) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____10169 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee1 p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p1, wopt, b))::rest -> begin
(

let uu____10240 = (matches_pat scrutinee1 p1)
in (match (uu____10240) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee1 rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
((log cfg (fun uu____10250 -> (

let uu____10251 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____10252 = (

let uu____10253 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right uu____10253 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" uu____10251 uu____10252)))));
(

let env2 = (FStar_List.fold_left (fun env2 t1 -> (

let uu____10262 = (

let uu____10263 = (

let uu____10273 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ((([]), (t1)))))
in (([]), (t1), (uu____10273), (false)))
in Clos (uu____10263))
in (uu____10262)::env2)) env1 s)
in (

let uu____10296 = (guard_when_clause wopt b rest)
in (norm cfg env2 stack2 uu____10296)));
)
end))
end))
in (

let uu____10297 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota))))
in (match (uu____10297) with
| true -> begin
(norm_and_rebuild_match ())
end
| uu____10298 -> begin
(matches scrutinee branches)
end))))))));
)
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun uu___140_10311 -> (match (uu___140_10311) with
| UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| Inlining -> begin
(FStar_TypeChecker_Env.Inlining)::[]
end
| uu____10314 -> begin
[]
end))))
in (

let d1 = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| uu____10318 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d1; primitive_steps = (FStar_List.append built_in_primitive_steps equality_ops)})))


let normalize_with_primitive_steps : primitive_step Prims.list  ->  step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun ps s e t -> (

let c = (config s e)
in (

let c1 = (

let uu___193_10338 = (config s e)
in {steps = uu___193_10338.steps; tcenv = uu___193_10338.tcenv; delta_level = uu___193_10338.delta_level; primitive_steps = (FStar_List.append c.primitive_steps ps)})
in (norm c1 [] [] t))))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (normalize_with_primitive_steps [] s e t))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (

let uu____10357 = (config s e)
in (norm_comp uu____10357 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let uu____10364 = (config [] env)
in (norm_universe uu____10364 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (

let uu____10371 = (config [] env)
in (ghost_to_pure_aux uu____10371 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (

let uu____10383 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____10383)))
in (

let uu____10384 = ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ))
in (match (uu____10384) with
| true -> begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let uu___194_10386 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = uu___194_10386.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___194_10386.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____10387 -> (

let uu____10388 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env uu____10388)))})
end
| FStar_Pervasives_Native.None -> begin
lc
end)
end
| uu____10389 -> begin
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

let uu____10401 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_warning "Normalization failed with error %s" uu____10401));
t;
)
end
in (FStar_Syntax_Print.term_to_string t1)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let c1 = try
(match (()) with
| () -> begin
(

let uu____10410 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp uu____10410 [] c))
end)
with
| e -> begin
((

let uu____10414 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_warning "Normalization failed with error %s" uu____10414));
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

let uu____10451 = (

let uu____10452 = (

let uu____10457 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (uu____10457)))
in FStar_Syntax_Syntax.Tm_refine (uu____10452))
in (mk uu____10451 t01.FStar_Syntax_Syntax.pos))
end
| uu____10462 -> begin
t2
end))
end
| uu____10463 -> begin
t2
end)))
in (aux t))))


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((WHNF)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Beta)::[]) env t))


let reduce_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((Beta)::(NoDeltaSteps)::(CompressUvars)::(Exclude (Zeta))::(Exclude (Iota))::(NoFullNorm)::[]) env t))


let eta_expand_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e t_e -> (

let uu____10485 = (FStar_Syntax_Util.arrow_formals_comp t_e)
in (match (uu____10485) with
| (formals, c) -> begin
(match (formals) with
| [] -> begin
e
end
| uu____10501 -> begin
(

let uu____10505 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____10505) with
| (actuals, uu____10516, uu____10517) -> begin
(match (((FStar_List.length actuals) = (FStar_List.length formals))) with
| true -> begin
e
end
| uu____10538 -> begin
(

let uu____10539 = (FStar_All.pipe_right formals FStar_Syntax_Util.args_of_binders)
in (match (uu____10539) with
| (binders, args) -> begin
(

let uu____10549 = (FStar_Syntax_Syntax.mk_Tm_app e args FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____10552 = (

let uu____10559 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_44 -> FStar_Util.Inl (_0_44)))
in (FStar_All.pipe_right uu____10559 (fun _0_45 -> FStar_Pervasives_Native.Some (_0_45))))
in (FStar_Syntax_Util.abs binders uu____10549 uu____10552)))
end))
end)
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____10595 = (

let uu____10599 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((uu____10599), (t.FStar_Syntax_Syntax.n)))
in (match (uu____10595) with
| (FStar_Pervasives_Native.Some (sort), uu____10606) -> begin
(

let uu____10608 = (mk sort t.FStar_Syntax_Syntax.pos)
in (eta_expand_with_type env t uu____10608))
end
| (uu____10609, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(eta_expand_with_type env t x.FStar_Syntax_Syntax.sort)
end
| uu____10613 -> begin
(

let uu____10617 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____10617) with
| (head1, args) -> begin
(

let uu____10643 = (

let uu____10644 = (FStar_Syntax_Subst.compress head1)
in uu____10644.FStar_Syntax_Syntax.n)
in (match (uu____10643) with
| FStar_Syntax_Syntax.Tm_uvar (uu____10647, thead) -> begin
(

let uu____10661 = (FStar_Syntax_Util.arrow_formals thead)
in (match (uu____10661) with
| (formals, tres) -> begin
(match (((FStar_List.length formals) = (FStar_List.length args))) with
| true -> begin
t
end
| uu____10691 -> begin
(

let uu____10692 = (env.FStar_TypeChecker_Env.type_of (

let uu___199_10696 = env
in {FStar_TypeChecker_Env.solver = uu___199_10696.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___199_10696.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___199_10696.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___199_10696.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___199_10696.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___199_10696.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___199_10696.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___199_10696.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___199_10696.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___199_10696.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___199_10696.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___199_10696.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___199_10696.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___199_10696.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___199_10696.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___199_10696.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___199_10696.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___199_10696.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___199_10696.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___199_10696.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___199_10696.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (uu____10692) with
| (uu____10697, ty, uu____10699) -> begin
(eta_expand_with_type env t ty)
end))
end)
end))
end
| uu____10700 -> begin
(

let uu____10701 = (env.FStar_TypeChecker_Env.type_of (

let uu___200_10705 = env
in {FStar_TypeChecker_Env.solver = uu___200_10705.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___200_10705.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___200_10705.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___200_10705.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___200_10705.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___200_10705.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___200_10705.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___200_10705.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___200_10705.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___200_10705.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___200_10705.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___200_10705.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___200_10705.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___200_10705.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___200_10705.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___200_10705.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___200_10705.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___200_10705.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___200_10705.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___200_10705.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___200_10705.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (uu____10701) with
| (uu____10706, ty, uu____10708) -> begin
(eta_expand_with_type env t ty)
end))
end))
end))
end)))




