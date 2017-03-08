
open Prims
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
| uu____10 -> begin
false
end))


let uu___is_Iota : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iota -> begin
true
end
| uu____14 -> begin
false
end))


let uu___is_Zeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Zeta -> begin
true
end
| uu____18 -> begin
false
end))


let uu___is_Exclude : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
true
end
| uu____23 -> begin
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
| uu____34 -> begin
false
end))


let uu___is_Primops : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____38 -> begin
false
end))


let uu___is_Eager_unfolding : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding -> begin
true
end
| uu____42 -> begin
false
end))


let uu___is_Inlining : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____46 -> begin
false
end))


let uu___is_NoDeltaSteps : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoDeltaSteps -> begin
true
end
| uu____50 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____55 -> begin
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
| uu____66 -> begin
false
end))


let uu___is_Simplify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simplify -> begin
true
end
| uu____70 -> begin
false
end))


let uu___is_EraseUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EraseUniverses -> begin
true
end
| uu____74 -> begin
false
end))


let uu___is_AllowUnboundUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AllowUnboundUniverses -> begin
true
end
| uu____78 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____82 -> begin
false
end))


let uu___is_CompressUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CompressUvars -> begin
true
end
| uu____86 -> begin
false
end))


let uu___is_NoFullNorm : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoFullNorm -> begin
true
end
| uu____90 -> begin
false
end))


type steps =
step Prims.list

type closure =
| Clos of (closure Prims.list * FStar_Syntax_Syntax.term * (closure Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
| Univ of FStar_Syntax_Syntax.universe
| Dummy


let uu___is_Clos : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Clos (_0) -> begin
true
end
| uu____120 -> begin
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
| uu____159 -> begin
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
| uu____170 -> begin
false
end))


type env =
closure Prims.list


let closure_to_string : closure  ->  Prims.string = (fun uu___124_174 -> (match (uu___124_174) with
| Clos (uu____175, t, uu____177, uu____178) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| Univ (uu____189) -> begin
"Univ"
end
| Dummy -> begin
"dummy"
end))

type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level Prims.list}


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list


type subst_t =
FStar_Syntax_Syntax.subst_elt Prims.list

type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option * FStar_Range.range)
| App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range)
| Let of (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range)
| Steps of (steps * FStar_TypeChecker_Env.delta_level Prims.list)
| Debug of FStar_Syntax_Syntax.term


let uu___is_Arg : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Arg (_0) -> begin
true
end
| uu____290 -> begin
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
| uu____314 -> begin
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
| uu____338 -> begin
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
| uu____365 -> begin
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
| uu____394 -> begin
false
end))


let __proj__Abs__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * env * (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Abs (_0) -> begin
_0
end))


let uu___is_App : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| App (_0) -> begin
true
end
| uu____433 -> begin
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
| uu____456 -> begin
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
| uu____478 -> begin
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
| uu____505 -> begin
false
end))


let __proj__Steps__item___0 : stack_elt  ->  (steps * FStar_TypeChecker_Env.delta_level Prims.list) = (fun projectee -> (match (projectee) with
| Steps (_0) -> begin
_0
end))


let uu___is_Debug : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
true
end
| uu____526 -> begin
false
end))


let __proj__Debug__item___0 : stack_elt  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
_0
end))


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (

let uu____574 = (FStar_ST.read r)
in (match (uu____574) with
| Some (uu____579) -> begin
(failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.write r (Some (t)))
end)))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (

let uu____588 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right uu____588 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun uu___125_593 -> (match (uu___125_593) with
| Arg (c, uu____595, uu____596) -> begin
(

let uu____597 = (closure_to_string c)
in (FStar_Util.format1 "Closure %s" uu____597))
end
| MemoLazy (uu____598) -> begin
"MemoLazy"
end
| Abs (uu____602, bs, uu____604, uu____605, uu____606) -> begin
(

let uu____613 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" uu____613))
end
| UnivArgs (uu____618) -> begin
"UnivArgs"
end
| Match (uu____622) -> begin
"Match"
end
| App (t, uu____627, uu____628) -> begin
(

let uu____629 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "App %s" uu____629))
end
| Meta (m, uu____631) -> begin
"Meta"
end
| Let (uu____632) -> begin
"Let"
end
| Steps (s, uu____638) -> begin
"Steps"
end
| Debug (t) -> begin
(

let uu____642 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Debug %s" uu____642))
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (

let uu____648 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right uu____648 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> (

let uu____662 = (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm")))
in (match (uu____662) with
| true -> begin
(f ())
end
| uu____663 -> begin
()
end)))


let is_empty = (fun uu___126_671 -> (match (uu___126_671) with
| [] -> begin
true
end
| uu____673 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| uu____691 -> begin
(

let uu____692 = (

let uu____693 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" uu____693))
in (failwith uu____692))
end)


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun l -> (match ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Ghost_lid)) with
| true -> begin
Some (FStar_Syntax_Const.effect_Pure_lid)
end
| uu____699 -> begin
(match ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
Some (FStar_Syntax_Const.effect_Tot_lid)
end
| uu____701 -> begin
(match ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid)) with
| true -> begin
Some (FStar_Syntax_Const.effect_PURE_lid)
end
| uu____703 -> begin
None
end)
end)
end))


let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let uu____724 = (FStar_List.fold_left (fun uu____733 u -> (match (uu____733) with
| (cur_kernel, cur_max, out) -> begin
(

let uu____748 = (FStar_Syntax_Util.univ_kernel u)
in (match (uu____748) with
| (k_u, n) -> begin
(

let uu____757 = (FStar_Syntax_Util.eq_univs cur_kernel k_u)
in (match (uu____757) with
| true -> begin
((cur_kernel), (u), (out))
end
| uu____763 -> begin
((k_u), (u), ((cur_max)::out))
end))
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (uu____724) with
| (uu____767, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
try
(match (()) with
| () -> begin
(

let uu____783 = (FStar_List.nth env x)
in (match (uu____783) with
| Univ (u) -> begin
(aux u)
end
| Dummy -> begin
(u)::[]
end
| uu____786 -> begin
(failwith "Impossible: universe variable bound to a term")
end))
end)
with
| uu____790 -> begin
(

let uu____791 = (FStar_All.pipe_right cfg.steps (FStar_List.contains AllowUnboundUniverses))
in (match (uu____791) with
| true -> begin
(FStar_Syntax_Syntax.U_unknown)::[]
end
| uu____793 -> begin
(failwith "Universe variable not found")
end))
end
end
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
(u)::[]
end
| FStar_Syntax_Syntax.U_max ([]) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let us = (

let uu____801 = (FStar_List.collect aux us)
in (FStar_All.pipe_right uu____801 norm_univs))
in (match (us) with
| (u_k)::(hd)::rest -> begin
(

let rest = (hd)::rest
in (

let uu____812 = (FStar_Syntax_Util.univ_kernel u_k)
in (match (uu____812) with
| (FStar_Syntax_Syntax.U_zero, n) -> begin
(

let uu____817 = (FStar_All.pipe_right rest (FStar_List.for_all (fun u -> (

let uu____820 = (FStar_Syntax_Util.univ_kernel u)
in (match (uu____820) with
| (uu____823, m) -> begin
(n <= m)
end)))))
in (match (uu____817) with
| true -> begin
rest
end
| uu____826 -> begin
us
end))
end
| uu____827 -> begin
us
end)))
end
| uu____830 -> begin
us
end))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(

let uu____833 = (aux u)
in (FStar_List.map (fun _0_33 -> FStar_Syntax_Syntax.U_succ (_0_33)) uu____833))
end)))
in (

let uu____835 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____835) with
| true -> begin
FStar_Syntax_Syntax.U_unknown
end
| uu____836 -> begin
(

let uu____837 = (aux u)
in (match (uu____837) with
| ([]) | ((FStar_Syntax_Syntax.U_zero)::[]) -> begin
FStar_Syntax_Syntax.U_zero
end
| (FStar_Syntax_Syntax.U_zero)::(u)::[] -> begin
u
end
| (FStar_Syntax_Syntax.U_zero)::us -> begin
FStar_Syntax_Syntax.U_max (us)
end
| (u)::[] -> begin
u
end
| us -> begin
FStar_Syntax_Syntax.U_max (us)
end))
end)))))


let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> ((log cfg (fun uu____934 -> (

let uu____935 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____936 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____935 uu____936)))));
(match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| uu____937 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____940) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (uu____964) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____974 = (

let uu____975 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (uu____975))
in (mk uu____974 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____982 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t uu____982))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____984 = (lookup_bvar env x)
in (match (uu____984) with
| Univ (uu____985) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, uu____989) -> begin
(closure_as_term cfg env t0)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (closure_as_term_delayed cfg env head)
in (

let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))) t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let uu____1057 = (closures_as_binders_delayed cfg env bs)
in (match (uu____1057) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (

let uu____1077 = (

let uu____1078 = (

let uu____1093 = (close_lcomp_opt cfg env lopt)
in ((bs), (body), (uu____1093)))
in FStar_Syntax_Syntax.Tm_abs (uu____1078))
in (mk uu____1077 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1123 = (closures_as_binders_delayed cfg env bs)
in (match (uu____1123) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____1154 = (

let uu____1161 = (

let uu____1165 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1165)::[])
in (closures_as_binders_delayed cfg env uu____1161))
in (match (uu____1154) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (

let uu____1179 = (

let uu____1180 = (

let uu____1185 = (

let uu____1186 = (FStar_List.hd x)
in (FStar_All.pipe_right uu____1186 Prims.fst))
in ((uu____1185), (phi)))
in FStar_Syntax_Syntax.Tm_refine (uu____1180))
in (mk uu____1179 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(

let uu____1216 = (

let uu____1217 = (

let uu____1230 = (closure_as_term_delayed cfg env t1)
in (

let uu____1233 = (

let uu____1240 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _0_34 -> FStar_Util.Inl (_0_34)) uu____1240))
in ((uu____1230), (uu____1233), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____1217))
in (mk uu____1216 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(

let uu____1285 = (

let uu____1286 = (

let uu____1299 = (closure_as_term_delayed cfg env t1)
in (

let uu____1302 = (

let uu____1309 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _0_35 -> FStar_Util.Inr (_0_35)) uu____1309))
in ((uu____1299), (uu____1302), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____1286))
in (mk uu____1285 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____1345 = (

let uu____1346 = (

let uu____1351 = (closure_as_term_delayed cfg env t')
in (

let uu____1354 = (

let uu____1355 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (uu____1355))
in ((uu____1351), (uu____1354))))
in FStar_Syntax_Syntax.Tm_meta (uu____1346))
in (mk uu____1345 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(

let uu____1397 = (

let uu____1398 = (

let uu____1403 = (closure_as_term_delayed cfg env t')
in (

let uu____1406 = (

let uu____1407 = (

let uu____1412 = (closure_as_term_delayed cfg env tbody)
in ((m), (uu____1412)))
in FStar_Syntax_Syntax.Meta_monadic (uu____1407))
in ((uu____1403), (uu____1406))))
in FStar_Syntax_Syntax.Tm_meta (uu____1398))
in (mk uu____1397 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody)) -> begin
(

let uu____1431 = (

let uu____1432 = (

let uu____1437 = (closure_as_term_delayed cfg env t')
in (

let uu____1440 = (

let uu____1441 = (

let uu____1447 = (closure_as_term_delayed cfg env tbody)
in ((m1), (m2), (uu____1447)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____1441))
in ((uu____1437), (uu____1440))))
in FStar_Syntax_Syntax.Tm_meta (uu____1432))
in (mk uu____1431 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(

let uu____1460 = (

let uu____1461 = (

let uu____1466 = (closure_as_term_delayed cfg env t')
in ((uu____1466), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____1461))
in (mk uu____1460 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env uu____1487 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____1498) -> begin
body
end
| FStar_Util.Inl (uu____1499) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let uu___138_1501 = lb
in {FStar_Syntax_Syntax.lbname = uu___138_1501.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___138_1501.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = uu___138_1501.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((uu____1508, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun uu____1532 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = (

let uu____1537 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____1537) with
| true -> begin
env_univs
end
| uu____1539 -> begin
(FStar_List.fold_right (fun uu____1541 env -> (Dummy)::env) lbs env_univs)
end))
in (

let uu___139_1544 = lb
in (

let uu____1545 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____1548 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___139_1544.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___139_1544.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____1545; FStar_Syntax_Syntax.lbeff = uu___139_1544.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____1548}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun uu____1559 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env uu____1614 -> (match (uu____1614) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____1660) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let uu____1680 = (norm_pat env hd)
in (match (uu____1680) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (

let uu____1716 = (norm_pat env p)
in (Prims.fst uu____1716)))))
in (((

let uu___140_1728 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = uu___140_1728.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___140_1728.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1745 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1779 uu____1780 -> (match (((uu____1779), (uu____1780))) with
| ((pats, env), (p, b)) -> begin
(

let uu____1845 = (norm_pat env p)
in (match (uu____1845) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (uu____1745) with
| (pats, env) -> begin
(((

let uu___141_1911 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = uu___141_1911.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___141_1911.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let uu___142_1925 = x
in (

let uu____1926 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___142_1925.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___142_1925.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1926}))
in (((

let uu___143_1932 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = uu___143_1932.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___143_1932.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let uu___144_1937 = x
in (

let uu____1938 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___144_1937.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___144_1937.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1938}))
in (((

let uu___145_1944 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = uu___145_1944.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___145_1944.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let uu___146_1954 = x
in (

let uu____1955 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___146_1954.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___146_1954.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1955}))
in (

let t = (closure_as_term cfg env t)
in (((

let uu___147_1962 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = uu___147_1962.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___147_1962.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let uu____1965 = (norm_pat env pat)
in (match (uu____1965) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____1989 = (closure_as_term cfg env w)
in Some (uu____1989))
end)
in (

let tm = (closure_as_term cfg env tm)
in ((pat), (w_opt), (tm))))
end)))
end))
in (

let uu____1994 = (

let uu____1995 = (

let uu____2011 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head), (uu____2011)))
in FStar_Syntax_Syntax.Tm_match (uu____1995))
in (mk uu____1994 t.FStar_Syntax_Syntax.pos))))
end))
end);
))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| uu____2064 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| uu____2080 -> begin
(FStar_List.map (fun uu____2090 -> (match (uu____2090) with
| (x, imp) -> begin
(

let uu____2105 = (closure_as_term_delayed cfg env x)
in ((uu____2105), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * closure Prims.list) = (fun cfg env bs -> (

let uu____2117 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2141 uu____2142 -> (match (((uu____2141), (uu____2142))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let uu___148_2186 = b
in (

let uu____2187 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___148_2186.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___148_2186.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2187}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (uu____2117) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| uu____2234 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____2246 = (closure_as_term_delayed cfg env t)
in (

let uu____2247 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____2246 uu____2247)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____2257 = (closure_as_term_delayed cfg env t)
in (

let uu____2258 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____2257 uu____2258)))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___127_2274 -> (match (uu___127_2274) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____2278 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (uu____2278))
end
| f -> begin
f
end))))
in (

let uu____2282 = (

let uu___149_2283 = c
in (

let uu____2284 = (FStar_List.map (norm_universe cfg env) c.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = uu____2284; FStar_Syntax_Syntax.effect_name = uu___149_2283.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp uu____2282)))))
end)
end))
and filter_out_lcomp_cflags : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun lc -> (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.filter (fun uu___128_2288 -> (match (uu___128_2288) with
| FStar_Syntax_Syntax.DECREASES (uu____2289) -> begin
false
end
| uu____2292 -> begin
true
end)))))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
(

let flags = (filter_out_lcomp_cflags lc)
in (

let uu____2320 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____2320) with
| true -> begin
Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), (flags))))
end
| uu____2336 -> begin
(

let uu____2337 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____2337) with
| true -> begin
Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), (flags))))
end
| uu____2353 -> begin
Some (FStar_Util.Inr (((lc.FStar_Syntax_Syntax.eff_name), (flags))))
end))
end)))
end
| uu____2363 -> begin
lopt
end))


let arith_ops : (FStar_Ident.lident * (Prims.int  ->  Prims.int  ->  FStar_Const.sconst)) Prims.list = (

let int_as_const = (fun i -> (

let uu____2381 = (

let uu____2387 = (FStar_Util.string_of_int i)
in ((uu____2387), (None)))
in FStar_Const.Const_int (uu____2381)))
in (

let bool_as_const = (fun b -> FStar_Const.Const_bool (b))
in (

let uu____2397 = (

let uu____2405 = (FStar_List.map (fun m -> (

let uu____2422 = (

let uu____2429 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("add")::[]))
in ((uu____2429), ((fun x y -> (int_as_const (x + y))))))
in (

let uu____2436 = (

let uu____2444 = (

let uu____2451 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((uu____2451), ((fun x y -> (int_as_const (x - y))))))
in (

let uu____2458 = (

let uu____2466 = (

let uu____2473 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((uu____2473), ((fun x y -> (int_as_const (x * y))))))
in (uu____2466)::[])
in (uu____2444)::uu____2458))
in (uu____2422)::uu____2436))) (("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]))
in (FStar_List.flatten uu____2405))
in (FStar_List.append ((((FStar_Syntax_Const.op_Addition), ((fun x y -> (int_as_const (x + y))))))::(((FStar_Syntax_Const.op_Subtraction), ((fun x y -> (int_as_const (x - y))))))::(((FStar_Syntax_Const.op_Multiply), ((fun x y -> (int_as_const (x * y))))))::(((FStar_Syntax_Const.op_Division), ((fun x y -> (int_as_const (x / y))))))::(((FStar_Syntax_Const.op_LT), ((fun x y -> (bool_as_const (x < y))))))::(((FStar_Syntax_Const.op_LTE), ((fun x y -> (bool_as_const (x <= y))))))::(((FStar_Syntax_Const.op_GT), ((fun x y -> (bool_as_const (x > y))))))::(((FStar_Syntax_Const.op_GTE), ((fun x y -> (bool_as_const (x >= y))))))::(((FStar_Syntax_Const.op_Modulus), ((fun x y -> (int_as_const (x mod y))))))::[]) uu____2397))))


let un_ops : (FStar_Ident.lident * (Prims.string  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)) Prims.list = (

let mk = (fun x -> (mk x FStar_Range.dummyRange))
in (

let name = (fun x -> (

let uu____2668 = (

let uu____2669 = (

let uu____2670 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv uu____2670 FStar_Syntax_Syntax.Delta_constant None))
in FStar_Syntax_Syntax.Tm_fvar (uu____2669))
in (mk uu____2668)))
in (

let ctor = (fun x -> (

let uu____2679 = (

let uu____2680 = (

let uu____2681 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv uu____2681 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in FStar_Syntax_Syntax.Tm_fvar (uu____2680))
in (mk uu____2679)))
in (

let uu____2682 = (

let uu____2689 = (FStar_Syntax_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((uu____2689), ((fun s -> (

let uu____2695 = (FStar_String.list_of_string s)
in (

let uu____2697 = (

let uu____2700 = (

let uu____2701 = (

let uu____2711 = (

let uu____2712 = (ctor (("Prims")::("Nil")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2712 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____2713 = (

let uu____2720 = (

let uu____2726 = (name (("FStar")::("Char")::("char")::[]))
in ((uu____2726), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (uu____2720)::[])
in ((uu____2711), (uu____2713))))
in FStar_Syntax_Syntax.Tm_app (uu____2701))
in (mk uu____2700))
in (FStar_List.fold_right (fun c a -> (

let uu____2754 = (

let uu____2755 = (

let uu____2765 = (

let uu____2766 = (ctor (("Prims")::("Cons")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2766 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____2767 = (

let uu____2774 = (

let uu____2780 = (name (("FStar")::("Char")::("char")::[]))
in ((uu____2780), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (

let uu____2786 = (

let uu____2793 = (

let uu____2799 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))))
in ((uu____2799), (None)))
in (uu____2793)::(((a), (None)))::[])
in (uu____2774)::uu____2786))
in ((uu____2765), (uu____2767))))
in FStar_Syntax_Syntax.Tm_app (uu____2755))
in (mk uu____2754))) uu____2695 uu____2697)))))))
in (uu____2682)::[]))))


let reduce_equality : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun tm -> (

let is_decidable_equality = (fun t -> (

let uu____2859 = (

let uu____2860 = (FStar_Syntax_Util.un_uinst t)
in uu____2860.FStar_Syntax_Syntax.n)
in (match (uu____2859) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Eq)
end
| uu____2864 -> begin
false
end)))
in (

let is_propositional_equality = (fun t -> (

let uu____2869 = (

let uu____2870 = (FStar_Syntax_Util.un_uinst t)
in uu____2870.FStar_Syntax_Syntax.n)
in (match (uu____2869) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)
end
| uu____2874 -> begin
false
end)))
in (match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (op_eq_inst, ((_typ, uu____2879))::((a1, uu____2881))::((a2, uu____2883))::[]) when (is_decidable_equality op_eq_inst) -> begin
(

let tt = (

let uu____2924 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____2924) with
| FStar_Syntax_Util.Equal -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) tm.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Util.NotEqual -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) tm.FStar_Syntax_Syntax.pos)
end
| uu____2927 -> begin
tm
end))
in tt)
end
| (FStar_Syntax_Syntax.Tm_app (eq2_inst, (_)::((a1, _))::((a2, _))::[])) | (FStar_Syntax_Syntax.Tm_app (eq2_inst, ((a1, _))::((a2, _))::[])) when (is_propositional_equality eq2_inst) -> begin
(

let tt = (

let uu____2999 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____2999) with
| FStar_Syntax_Util.Equal -> begin
FStar_Syntax_Util.t_true
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Syntax_Util.t_false
end
| uu____3000 -> begin
tm
end))
in tt)
end
| uu____3001 -> begin
tm
end))))


let find_fv = (fun fv ops -> (match (fv.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.tryFind (fun uu____3026 -> (match (uu____3026) with
| (l, uu____3030) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv l)
end)) ops)
end
| uu____3031 -> begin
None
end))


let reduce_primops : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let uu____3048 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops steps))
in (match (uu____3048) with
| true -> begin
tm
end
| uu____3051 -> begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, uu____3056))::((a2, uu____3058))::[]) -> begin
(

let uu____3088 = (find_fv fv arith_ops)
in (match (uu____3088) with
| None -> begin
tm
end
| Some (uu____3108, op) -> begin
(

let norm = (fun i j -> (

let c = (

let uu____3134 = (FStar_Util.int_of_string i)
in (

let uu____3135 = (FStar_Util.int_of_string j)
in (op uu____3134 uu____3135)))
in (mk (FStar_Syntax_Syntax.Tm_constant (c)) tm.FStar_Syntax_Syntax.pos)))
in (

let uu____3136 = (

let uu____3139 = (

let uu____3140 = (FStar_Syntax_Subst.compress a1)
in uu____3140.FStar_Syntax_Syntax.n)
in (

let uu____3143 = (

let uu____3144 = (FStar_Syntax_Subst.compress a2)
in uu____3144.FStar_Syntax_Syntax.n)
in ((uu____3139), (uu____3143))))
in (match (uu____3136) with
| (FStar_Syntax_Syntax.Tm_app (head1, ((arg1, uu____3151))::[]), FStar_Syntax_Syntax.Tm_app (head2, ((arg2, uu____3154))::[])) -> begin
(

let uu____3197 = (

let uu____3202 = (

let uu____3203 = (FStar_Syntax_Subst.compress head1)
in uu____3203.FStar_Syntax_Syntax.n)
in (

let uu____3206 = (

let uu____3207 = (FStar_Syntax_Subst.compress head2)
in uu____3207.FStar_Syntax_Syntax.n)
in (

let uu____3210 = (

let uu____3211 = (FStar_Syntax_Subst.compress arg1)
in uu____3211.FStar_Syntax_Syntax.n)
in (

let uu____3214 = (

let uu____3215 = (FStar_Syntax_Subst.compress arg2)
in uu____3215.FStar_Syntax_Syntax.n)
in ((uu____3202), (uu____3206), (uu____3210), (uu____3214))))))
in (match (uu____3197) with
| (FStar_Syntax_Syntax.Tm_fvar (fv1), FStar_Syntax_Syntax.Tm_fvar (fv2), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) when ((FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") && (FStar_Util.ends_with (FStar_Ident.text_of_lid fv2.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t")) -> begin
(

let uu____3242 = (mk (FStar_Syntax_Syntax.Tm_fvar (fv1)) tm.FStar_Syntax_Syntax.pos)
in (

let uu____3245 = (

let uu____3251 = (

let uu____3257 = (norm i j)
in ((uu____3257), (None)))
in (uu____3251)::[])
in (FStar_Syntax_Util.mk_app uu____3242 uu____3245)))
end
| uu____3273 -> begin
tm
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) -> begin
(norm i j)
end
| uu____3290 -> begin
tm
end)))
end))
end
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, uu____3295))::[]) -> begin
(

let uu____3317 = (find_fv fv un_ops)
in (match (uu____3317) with
| None -> begin
tm
end
| Some (uu____3337, op) -> begin
(

let uu____3353 = (

let uu____3354 = (FStar_Syntax_Subst.compress a1)
in uu____3354.FStar_Syntax_Syntax.n)
in (match (uu____3353) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (b, uu____3360)) -> begin
(

let uu____3363 = (FStar_Bytes.unicode_bytes_as_string b)
in (op uu____3363))
end
| uu____3364 -> begin
tm
end))
end))
end
| uu____3365 -> begin
(reduce_equality tm)
end)
end)))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let uu___150_3390 = t
in {FStar_Syntax_Syntax.n = uu___150_3390.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___150_3390.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___150_3390.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| uu____3409 -> begin
None
end))
in (

let simplify = (fun arg -> (((simp_t (Prims.fst arg))), (arg)))
in (

let uu____3436 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps))
in (match (uu____3436) with
| true -> begin
(reduce_primops steps tm)
end
| uu____3439 -> begin
(match (tm.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) -> begin
(

let uu____3480 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid)
in (match (uu____3480) with
| true -> begin
(

let uu____3483 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____3483) with
| (((Some (true), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (true), _))::[]) -> begin
arg
end
| (((Some (false), _))::(_)::[]) | ((_)::((Some (false), _))::[]) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____3651 -> begin
tm
end))
end
| uu____3660 -> begin
(

let uu____3661 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid)
in (match (uu____3661) with
| true -> begin
(

let uu____3664 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____3664) with
| (((Some (true), _))::(_)::[]) | ((_)::((Some (true), _))::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (((Some (false), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (false), _))::[]) -> begin
arg
end
| uu____3832 -> begin
tm
end))
end
| uu____3841 -> begin
(

let uu____3842 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid)
in (match (uu____3842) with
| true -> begin
(

let uu____3845 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____3845) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), uu____3936))::((uu____3937, (arg, uu____3939)))::[] -> begin
arg
end
| uu____3980 -> begin
tm
end))
end
| uu____3989 -> begin
(

let uu____3990 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid)
in (match (uu____3990) with
| true -> begin
(

let uu____3993 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____3993) with
| ((Some (true), uu____4028))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), uu____4052))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____4076 -> begin
tm
end))
end
| uu____4085 -> begin
(

let uu____4086 = ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid))
in (match (uu____4086) with
| true -> begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(

let uu____4131 = (

let uu____4132 = (FStar_Syntax_Subst.compress t)
in uu____4132.FStar_Syntax_Syntax.n)
in (match (uu____4131) with
| FStar_Syntax_Syntax.Tm_abs ((uu____4137)::[], body, uu____4139) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____4167 -> begin
tm
end)
end
| uu____4169 -> begin
tm
end))
end
| uu____4170 -> begin
tm
end)
end
| uu____4176 -> begin
(reduce_equality tm)
end))
end))
end))
end))
end))
end
| uu____4177 -> begin
tm
end)
end))))))


let is_norm_request = (fun hd args -> (

let uu____4192 = (

let uu____4196 = (

let uu____4197 = (FStar_Syntax_Util.un_uinst hd)
in uu____4197.FStar_Syntax_Syntax.n)
in ((uu____4196), (args)))
in (match (uu____4192) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4202)::(uu____4203)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4206)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize)
end
| uu____4208 -> begin
false
end)))


let get_norm_request = (fun args -> (match (args) with
| ((_)::((tm, _))::[]) | (((tm, _))::[]) -> begin
tm
end
| uu____4241 -> begin
(failwith "Impossible")
end))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let firstn = (fun k l -> (match (((FStar_List.length l) < k)) with
| true -> begin
((l), ([]))
end
| uu____4358 -> begin
(FStar_Util.first_N k l)
end))
in ((log cfg (fun uu____4360 -> (

let uu____4361 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____4362 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____4363 = (

let uu____4364 = (

let uu____4366 = (firstn (Prims.parse_int "4") stack)
in (FStar_All.pipe_left Prims.fst uu____4366))
in (stack_to_string uu____4364))
in (FStar_Util.print3 ">>> %s\nNorm %s with top of the stack %s \n" uu____4361 uu____4362 uu____4363))))));
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____4378) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app (hd, args) when (((

let uu____4425 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoFullNorm))
in (not (uu____4425))) && (is_norm_request hd args)) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid)))) -> begin
(

let tm = (get_norm_request args)
in (

let s = (Reify)::(Beta)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Zeta)::(Iota)::(Primops)::[]
in (

let cfg' = (

let uu___151_4438 = cfg
in {steps = s; tcenv = uu___151_4438.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]})
in (

let stack' = (Debug (t))::(Steps (((cfg.steps), (cfg.delta_level))))::stack
in (norm cfg' env stack' tm)))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____4442; FStar_Syntax_Syntax.pos = uu____4443; FStar_Syntax_Syntax.vars = uu____4444}, (a1)::(a2)::rest) -> begin
(

let uu____4478 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____4478) with
| (hd, uu____4489) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____4544; FStar_Syntax_Syntax.pos = uu____4545; FStar_Syntax_Syntax.vars = uu____4546}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let uu____4569 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____4569) with
| (reify_head, uu____4580) -> begin
(

let a = (

let uu____4596 = (FStar_All.pipe_left FStar_Syntax_Util.unascribe (Prims.fst a))
in (FStar_Syntax_Subst.compress uu____4596))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4599)); FStar_Syntax_Syntax.tk = uu____4600; FStar_Syntax_Syntax.pos = uu____4601; FStar_Syntax_Syntax.vars = uu____4602}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| uu____4627 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (

let uu____4635 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack uu____4635)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let uu____4642 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____4642) with
| true -> begin
(norm cfg env stack t')
end
| uu____4643 -> begin
(

let us = (

let uu____4645 = (

let uu____4649 = (FStar_List.map (norm_universe cfg env) us)
in ((uu____4649), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (uu____4645))
in (

let stack = (us)::stack
in (norm cfg env stack t')))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t
in (

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun uu___129_4658 -> (match (uu___129_4658) with
| FStar_TypeChecker_Env.NoDelta -> begin
false
end
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| FStar_TypeChecker_Env.Unfold (l) -> begin
(FStar_TypeChecker_Common.delta_depth_greater_than f.FStar_Syntax_Syntax.fv_delta l)
end))))
in (match ((not (should_delta))) with
| true -> begin
(rebuild cfg env stack t)
end
| uu____4660 -> begin
(

let r_env = (

let uu____4662 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv uu____4662))
in (

let uu____4663 = (FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____4663) with
| None -> begin
((log cfg (fun uu____4674 -> (FStar_Util.print "Tm_fvar case 2\n" [])));
(rebuild cfg env stack t);
)
end
| Some (us, t) -> begin
((log cfg (fun uu____4680 -> (

let uu____4681 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____4682 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____4681 uu____4682)))));
(

let n = (FStar_List.length us)
in (match ((n > (Prims.parse_int "0"))) with
| true -> begin
(match (stack) with
| (UnivArgs (us', uu____4689))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| uu____4702 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| uu____4703 -> begin
(

let uu____4704 = (

let uu____4705 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" uu____4705))
in (failwith uu____4704))
end)
end
| uu____4710 -> begin
(norm cfg env stack t)
end));
)
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____4712 = (lookup_bvar env x)
in (match (uu____4712) with
| Univ (uu____4713) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env, t0, r, fix) -> begin
(match (((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps))))) with
| true -> begin
(

let uu____4728 = (FStar_ST.read r)
in (match (uu____4728) with
| Some (env, t') -> begin
((log cfg (fun uu____4747 -> (

let uu____4748 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____4749 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" uu____4748 uu____4749)))));
(

let uu____4750 = (

let uu____4751 = (FStar_Syntax_Subst.compress t')
in uu____4751.FStar_Syntax_Syntax.n)
in (match (uu____4750) with
| FStar_Syntax_Syntax.Tm_abs (uu____4754) -> begin
(norm cfg env stack t')
end
| uu____4769 -> begin
(rebuild cfg env stack t')
end));
)
end
| None -> begin
(norm cfg env ((MemoLazy (r))::stack) t0)
end))
end
| uu____4776 -> begin
(norm cfg env stack t0)
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack) with
| (UnivArgs (uu____4802))::uu____4803 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (uu____4808))::uu____4809 -> begin
(failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, uu____4815, uu____4816))::stack_rest -> begin
(match (c) with
| Univ (uu____4819) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| uu____4820 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (uu____4823)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
((log cfg (fun uu____4836 -> (

let uu____4837 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____4837))));
(norm cfg ((c)::env) stack_rest body);
)
end
| Some (FStar_Util.Inr (l, cflags)) when (((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right cflags (FStar_Util.for_some (fun uu___130_4851 -> (match (uu___130_4851) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____4852 -> begin
false
end))))) -> begin
((log cfg (fun uu____4854 -> (

let uu____4855 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____4855))));
(norm cfg ((c)::env) stack_rest body);
)
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
((log cfg (fun uu____4866 -> (

let uu____4867 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____4867))));
(norm cfg ((c)::env) stack_rest body);
)
end
| uu____4868 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| uu____4875 -> begin
(

let cfg = (

let uu___152_4883 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = uu___152_4883.tcenv; delta_level = uu___152_4883.delta_level})
in (

let uu____4884 = (closure_as_term cfg env t)
in (rebuild cfg env stack uu____4884)))
end)
end
| (uu____4885)::tl -> begin
((log cfg (fun uu____4895 -> (

let uu____4896 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____4896))));
(

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body));
)
end)
end)
end
| (Steps (s, dl))::stack -> begin
(norm (

let uu___153_4917 = cfg
in {steps = s; tcenv = uu___153_4917.tcenv; delta_level = dl}) env stack t)
end
| (MemoLazy (r))::stack -> begin
((set_memo r ((env), (t)));
(log cfg (fun uu____4930 -> (

let uu____4931 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" uu____4931))));
(norm cfg env stack t);
)
end
| ((Debug (_))::_) | ((Meta (_))::_) | ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____4942 = (closure_as_term cfg env t)
in (rebuild cfg env stack uu____4942))
end
| uu____4943 -> begin
(

let uu____4944 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____4944) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(

let uu____4973 = (

let uu____4979 = (

let uu____4980 = (

let uu____4981 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____4981))
in (FStar_All.pipe_right uu____4980 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____4979 (fun _0_36 -> FStar_Util.Inl (_0_36))))
in (FStar_All.pipe_right uu____4973 (fun _0_37 -> Some (_0_37))))
end
| uu____5006 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env uu____5020 -> (Dummy)::env) env))
in ((log cfg (fun uu____5025 -> (

let uu____5026 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____5026))));
(norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body);
)))
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____5060 stack -> (match (uu____5060) with
| (a, aq) -> begin
(

let uu____5068 = (

let uu____5069 = (

let uu____5073 = (

let uu____5074 = (

let uu____5084 = (FStar_Util.mk_ref None)
in ((env), (a), (uu____5084), (false)))
in Clos (uu____5074))
in ((uu____5073), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (uu____5069))
in (uu____5068)::stack)
end)) args))
in ((log cfg (fun uu____5106 -> (

let uu____5107 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____5107))));
(norm cfg env stack head);
))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(match (((env), (stack))) with
| ([], []) -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_refine ((((

let uu___154_5128 = x
in {FStar_Syntax_Syntax.ppname = uu___154_5128.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___154_5128.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| uu____5129 -> begin
(

let uu____5132 = (closure_as_term cfg env t)
in (rebuild cfg env stack uu____5132))
end)
end
| uu____5133 -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let uu____5135 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (uu____5135) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (

let uu____5151 = (

let uu____5152 = (

let uu____5157 = (FStar_Syntax_Subst.close closing f)
in (((

let uu___155_5158 = x
in {FStar_Syntax_Syntax.ppname = uu___155_5158.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___155_5158.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (uu____5157)))
in FStar_Syntax_Syntax.Tm_refine (uu____5152))
in (mk uu____5151 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let uu____5171 = (closure_as_term cfg env t)
in (rebuild cfg env stack uu____5171))
end
| uu____5172 -> begin
(

let uu____5173 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____5173) with
| (bs, c) -> begin
(

let c = (

let uu____5179 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env uu____5185 -> (Dummy)::env) env))
in (norm_comp cfg uu____5179 c))
in (

let t = (

let uu____5192 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow uu____5192 c))
in (rebuild cfg env stack t)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _, _))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| uu____5231 -> begin
(

let t1 = (norm cfg env [] t1)
in ((log cfg (fun uu____5234 -> (FStar_Util.print_string "+++ Normalizing ascription \n")));
(

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(

let uu____5247 = (norm cfg env [] t)
in FStar_Util.Inl (uu____5247))
end
| FStar_Util.Inr (c) -> begin
(

let uu____5255 = (norm_comp cfg env c)
in FStar_Util.Inr (uu____5255))
end)
in (

let uu____5256 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack uu____5256)));
))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((uu____5301, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____5302); FStar_Syntax_Syntax.lbunivs = uu____5303; FStar_Syntax_Syntax.lbtyp = uu____5304; FStar_Syntax_Syntax.lbeff = uu____5305; FStar_Syntax_Syntax.lbdef = uu____5306})::uu____5307), uu____5308) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in (

let uu____5334 = ((

let uu____5335 = (FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps))
in (not (uu____5335))) && ((FStar_Syntax_Util.is_pure_effect n) || ((FStar_Syntax_Util.is_ghost_effect n) && (

let uu____5336 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (not (uu____5336))))))
in (match (uu____5334) with
| true -> begin
(

let env = (

let uu____5339 = (

let uu____5340 = (

let uu____5350 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (uu____5350), (false)))
in Clos (uu____5340))
in (uu____5339)::env)
in (norm cfg env stack body))
end
| uu____5373 -> begin
(

let uu____5374 = (

let uu____5377 = (

let uu____5378 = (

let uu____5379 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right uu____5379 FStar_Syntax_Syntax.mk_binder))
in (uu____5378)::[])
in (FStar_Syntax_Subst.open_term uu____5377 body))
in (match (uu____5374) with
| (bs, body) -> begin
(

let lb = (

let uu___156_5385 = lb
in (

let uu____5386 = (

let uu____5389 = (

let uu____5390 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____5390 Prims.fst))
in (FStar_All.pipe_right uu____5389 (fun _0_38 -> FStar_Util.Inl (_0_38))))
in (

let uu____5399 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____5402 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu____5386; FStar_Syntax_Syntax.lbunivs = uu___156_5385.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____5399; FStar_Syntax_Syntax.lbeff = uu___156_5385.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5402}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env uu____5412 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(

let uu____5428 = (closure_as_term cfg env t)
in (rebuild cfg env stack uu____5428))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let uu____5441 = (FStar_List.fold_right (fun lb uu____5463 -> (match (uu____5463) with
| (rec_env, memos, i) -> begin
(

let f_i = (

let uu____5502 = (

let uu___157_5503 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___157_5503.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___157_5503.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm uu____5502))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (Prims.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (uu____5441) with
| (rec_env, memos, uu____5563) -> begin
(

let uu____5578 = (FStar_List.map2 (fun lb memo -> (FStar_ST.write memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (

let uu____5620 = (

let uu____5621 = (

let uu____5631 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (uu____5631), (false)))
in Clos (uu____5621))
in (uu____5620)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let should_reify = (match (stack) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____5669; FStar_Syntax_Syntax.pos = uu____5670; FStar_Syntax_Syntax.vars = uu____5671}, uu____5672, uu____5673))::uu____5674 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____5680 -> begin
false
end)
in (match ((not (should_reify))) with
| true -> begin
(

let t = (norm cfg env [] t)
in (

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let uu____5686 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____5686) with
| true -> begin
(

let uu___158_5687 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = uu___158_5687.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]})
end
| uu____5688 -> begin
(

let uu___159_5689 = cfg
in {steps = (FStar_List.append ((NoDeltaSteps)::(Exclude (Zeta))::[]) cfg.steps); tcenv = uu___159_5689.tcenv; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]})
end))
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m), (t)))), (t.FStar_Syntax_Syntax.pos))))::stack) head))))
end
| uu____5690 -> begin
(

let uu____5691 = (

let uu____5692 = (FStar_Syntax_Subst.compress head)
in uu____5692.FStar_Syntax_Syntax.n)
in (match (uu____5691) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let uu____5706 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____5706) with
| (uu____5707, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____5711) -> begin
(failwith "Cannot reify a top-level let binding")
end
| FStar_Util.Inl (x) -> begin
(

let is_return = (fun e -> (

let uu____5718 = (

let uu____5719 = (FStar_Syntax_Subst.compress e)
in uu____5719.FStar_Syntax_Syntax.n)
in (match (uu____5718) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (uu____5724, uu____5725)) -> begin
(

let uu____5734 = (

let uu____5735 = (FStar_Syntax_Subst.compress e)
in uu____5735.FStar_Syntax_Syntax.n)
in (match (uu____5734) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (uu____5740, msrc, uu____5742)) when (FStar_Syntax_Util.is_pure_effect msrc) -> begin
(

let uu____5751 = (FStar_Syntax_Subst.compress e)
in Some (uu____5751))
end
| uu____5752 -> begin
None
end))
end
| uu____5753 -> begin
None
end)))
in (

let uu____5754 = (is_return lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____5754) with
| Some (e) -> begin
(

let lb = (

let uu___160_5758 = lb
in {FStar_Syntax_Syntax.lbname = uu___160_5758.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___160_5758.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___160_5758.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = e})
in (

let uu____5759 = (FStar_List.tl stack)
in (

let uu____5760 = (

let uu____5761 = (

let uu____5764 = (

let uu____5765 = (

let uu____5773 = (FStar_Syntax_Util.mk_reify body)
in ((((false), ((lb)::[]))), (uu____5773)))
in FStar_Syntax_Syntax.Tm_let (uu____5765))
in (FStar_Syntax_Syntax.mk uu____5764))
in (uu____5761 None head.FStar_Syntax_Syntax.pos))
in (norm cfg env uu____5759 uu____5760))))
end
| None -> begin
(

let uu____5790 = (

let uu____5791 = (is_return body)
in (match (uu____5791) with
| Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_bvar (y); FStar_Syntax_Syntax.tk = uu____5794; FStar_Syntax_Syntax.pos = uu____5795; FStar_Syntax_Syntax.vars = uu____5796}) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____5801 -> begin
false
end))
in (match (uu____5790) with
| true -> begin
(norm cfg env stack lb.FStar_Syntax_Syntax.lbdef)
end
| uu____5803 -> begin
(

let head = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify body)
in (

let body = (

let uu____5821 = (

let uu____5824 = (

let uu____5825 = (

let uu____5840 = (

let uu____5842 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____5842)::[])
in ((uu____5840), (body), (Some (FStar_Util.Inr (((m), ([])))))))
in FStar_Syntax_Syntax.Tm_abs (uu____5825))
in (FStar_Syntax_Syntax.mk uu____5824))
in (uu____5821 None body.FStar_Syntax_Syntax.pos))
in (

let bind_inst = (

let uu____5872 = (

let uu____5873 = (FStar_Syntax_Subst.compress bind_repr)
in uu____5873.FStar_Syntax_Syntax.n)
in (match (uu____5872) with
| FStar_Syntax_Syntax.Tm_uinst (bind, (uu____5879)::(uu____5880)::[]) -> begin
(

let uu____5886 = (

let uu____5889 = (

let uu____5890 = (

let uu____5895 = (

let uu____5897 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____5898 = (

let uu____5900 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv t)
in (uu____5900)::[])
in (uu____5897)::uu____5898))
in ((bind), (uu____5895)))
in FStar_Syntax_Syntax.Tm_uinst (uu____5890))
in (FStar_Syntax_Syntax.mk uu____5889))
in (uu____5886 None t.FStar_Syntax_Syntax.pos))
end
| uu____5912 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let reified = (

let uu____5918 = (

let uu____5921 = (

let uu____5922 = (

let uu____5932 = (

let uu____5934 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____5935 = (

let uu____5937 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____5938 = (

let uu____5940 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____5941 = (

let uu____5943 = (FStar_Syntax_Syntax.as_arg head)
in (

let uu____5944 = (

let uu____5946 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____5947 = (

let uu____5949 = (FStar_Syntax_Syntax.as_arg body)
in (uu____5949)::[])
in (uu____5946)::uu____5947))
in (uu____5943)::uu____5944))
in (uu____5940)::uu____5941))
in (uu____5937)::uu____5938))
in (uu____5934)::uu____5935))
in ((bind_inst), (uu____5932)))
in FStar_Syntax_Syntax.Tm_app (uu____5922))
in (FStar_Syntax_Syntax.mk uu____5921))
in (uu____5918 None t.FStar_Syntax_Syntax.pos))
in (

let uu____5961 = (FStar_List.tl stack)
in (norm cfg env uu____5961 reified)))))))
end))
end)))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let uu____5979 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____5979) with
| (uu____5980, bind_repr) -> begin
(

let maybe_unfold_action = (fun head -> (

let maybe_extract_fv = (fun t -> (

let t = (

let uu____6003 = (

let uu____6004 = (FStar_Syntax_Subst.compress t)
in uu____6004.FStar_Syntax_Syntax.n)
in (match (uu____6003) with
| FStar_Syntax_Syntax.Tm_uinst (t, uu____6010) -> begin
t
end
| uu____6015 -> begin
head
end))
in (

let uu____6016 = (

let uu____6017 = (FStar_Syntax_Subst.compress t)
in uu____6017.FStar_Syntax_Syntax.n)
in (match (uu____6016) with
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
Some (x)
end
| uu____6022 -> begin
None
end))))
in (

let uu____6023 = (maybe_extract_fv head)
in (match (uu____6023) with
| Some (x) when (

let uu____6029 = (FStar_Syntax_Syntax.lid_of_fv x)
in (FStar_TypeChecker_Env.is_action cfg.tcenv uu____6029)) -> begin
(

let head = (norm cfg env [] head)
in (

let action_unfolded = (

let uu____6033 = (maybe_extract_fv head)
in (match (uu____6033) with
| Some (uu____6036) -> begin
Some (true)
end
| uu____6037 -> begin
Some (false)
end))
in ((head), (action_unfolded))))
end
| uu____6040 -> begin
((head), (None))
end))))
in (

let rec bind_on_lift = (fun args acc -> (match (args) with
| [] -> begin
(match ((FStar_List.rev acc)) with
| [] -> begin
(failwith "bind_on_lift should be always called with a non-empty list")
end
| ((head, uu____6087))::args -> begin
(

let uu____6102 = (maybe_unfold_action head)
in (match (uu____6102) with
| (head, found_action) -> begin
(

let mk = (fun tm -> ((FStar_Syntax_Syntax.mk tm) None t.FStar_Syntax_Syntax.pos))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))))
in (match (found_action) with
| None -> begin
(FStar_Syntax_Util.mk_reify body)
end
| Some (false) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))))
end
| Some (true) -> begin
body
end)))
end))
end)
end
| ((e, q))::es -> begin
(

let uu____6148 = (

let uu____6149 = (FStar_Syntax_Subst.compress e)
in uu____6149.FStar_Syntax_Syntax.n)
in (match (uu____6148) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t')) when (not ((FStar_Syntax_Util.is_pure_effect m1))) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "monadic_app_var" None t')
in (

let body = (

let uu____6170 = (

let uu____6176 = (

let uu____6179 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____6179), (q)))
in (uu____6176)::acc)
in (bind_on_lift es uu____6170))
in (

let lifted_e0 = (reify_lift cfg.tcenv e0 m1 m2 t')
in (

let continuation = (FStar_Syntax_Util.abs ((((x), (None)))::[]) body (Some (FStar_Util.Inr (((m2), ([]))))))
in (

let bind_inst = (

let uu____6203 = (

let uu____6204 = (FStar_Syntax_Subst.compress bind_repr)
in uu____6204.FStar_Syntax_Syntax.n)
in (match (uu____6203) with
| FStar_Syntax_Syntax.Tm_uinst (bind, (uu____6210)::(uu____6211)::[]) -> begin
(

let uu____6217 = (

let uu____6220 = (

let uu____6221 = (

let uu____6226 = (

let uu____6228 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv t')
in (

let uu____6229 = (

let uu____6231 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv t)
in (uu____6231)::[])
in (uu____6228)::uu____6229))
in ((bind), (uu____6226)))
in FStar_Syntax_Syntax.Tm_uinst (uu____6221))
in (FStar_Syntax_Syntax.mk uu____6220))
in (uu____6217 None e0.FStar_Syntax_Syntax.pos))
end
| uu____6243 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let uu____6246 = (

let uu____6249 = (

let uu____6250 = (

let uu____6260 = (

let uu____6262 = (FStar_Syntax_Syntax.as_arg t')
in (

let uu____6263 = (

let uu____6265 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____6266 = (

let uu____6268 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____6269 = (

let uu____6271 = (FStar_Syntax_Syntax.as_arg lifted_e0)
in (

let uu____6272 = (

let uu____6274 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____6275 = (

let uu____6277 = (FStar_Syntax_Syntax.as_arg continuation)
in (uu____6277)::[])
in (uu____6274)::uu____6275))
in (uu____6271)::uu____6272))
in (uu____6268)::uu____6269))
in (uu____6265)::uu____6266))
in (uu____6262)::uu____6263))
in ((bind_inst), (uu____6260)))
in FStar_Syntax_Syntax.Tm_app (uu____6250))
in (FStar_Syntax_Syntax.mk uu____6249))
in (uu____6246 None e0.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (uu____6290)) -> begin
(bind_on_lift es ((((e0), (q)))::acc))
end
| uu____6306 -> begin
(bind_on_lift es ((((e), (q)))::acc))
end))
end))
in (

let binded_head = (

let uu____6312 = (

let uu____6316 = (FStar_Syntax_Syntax.as_arg head)
in (uu____6316)::args)
in (bind_on_lift uu____6312 []))
in (

let uu____6321 = (FStar_List.tl stack)
in (norm cfg env uu____6321 binded_head)))))
end)))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (reify_lift cfg.tcenv e msrc mtgt t')
in (

let uu____6335 = (FStar_List.tl stack)
in (norm cfg env uu____6335 lifted)))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun uu____6418 -> (match (uu____6418) with
| (pat, wopt, tm) -> begin
(

let uu____6456 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____6456)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches)))) t.FStar_Syntax_Syntax.pos)
in (

let uu____6482 = (FStar_List.tl stack)
in (norm cfg env uu____6482 tm))))
end
| uu____6483 -> begin
(norm cfg env stack head)
end))
end))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) -> begin
(

let should_reify = (match (stack) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____6492; FStar_Syntax_Syntax.pos = uu____6493; FStar_Syntax_Syntax.vars = uu____6494}, uu____6495, uu____6496))::uu____6497 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____6503 -> begin
false
end)
in (match (should_reify) with
| true -> begin
(

let uu____6504 = (FStar_List.tl stack)
in (

let uu____6505 = (reify_lift cfg.tcenv head m m' t)
in (norm cfg env uu____6504 uu____6505)))
end
| uu____6506 -> begin
(

let uu____6507 = (((FStar_Syntax_Util.is_pure_effect m) || (FStar_Syntax_Util.is_ghost_effect m)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)))
in (match (uu____6507) with
| true -> begin
(

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let uu___161_6512 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = uu___161_6512.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m'), (t)))), (head.FStar_Syntax_Syntax.pos))))::stack) head)))
end
| uu____6515 -> begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m'), (t)))), (head.FStar_Syntax_Syntax.pos))))::stack) head)
end))
end))
end
| uu____6518 -> begin
(match (stack) with
| (uu____6519)::uu____6520 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____6524) -> begin
(norm cfg env ((Meta (((m), (r))))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args)), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| uu____6539 -> begin
(norm cfg env stack head)
end)
end
| uu____6540 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let uu____6550 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (uu____6550))
end
| uu____6557 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end)
end);
))))
and reify_lift : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.monad_name  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env e msrc mtgt t -> (match ((FStar_Syntax_Util.is_pure_effect msrc)) with
| true -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl env mtgt)
in (

let uu____6571 = ed.FStar_Syntax_Syntax.return_repr
in (match (uu____6571) with
| (uu____6572, return_repr) -> begin
(

let return_inst = (

let uu____6579 = (

let uu____6580 = (FStar_Syntax_Subst.compress return_repr)
in uu____6580.FStar_Syntax_Syntax.n)
in (match (uu____6579) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (uu____6586)::[]) -> begin
(

let uu____6592 = (

let uu____6595 = (

let uu____6596 = (

let uu____6601 = (

let uu____6603 = (env.FStar_TypeChecker_Env.universe_of env t)
in (uu____6603)::[])
in ((return_tm), (uu____6601)))
in FStar_Syntax_Syntax.Tm_uinst (uu____6596))
in (FStar_Syntax_Syntax.mk uu____6595))
in (uu____6592 None e.FStar_Syntax_Syntax.pos))
end
| uu____6615 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let uu____6618 = (

let uu____6621 = (

let uu____6622 = (

let uu____6632 = (

let uu____6634 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____6635 = (

let uu____6637 = (FStar_Syntax_Syntax.as_arg e)
in (uu____6637)::[])
in (uu____6634)::uu____6635))
in ((return_inst), (uu____6632)))
in FStar_Syntax_Syntax.Tm_app (uu____6622))
in (FStar_Syntax_Syntax.mk uu____6621))
in (uu____6618 None e.FStar_Syntax_Syntax.pos)))
end)))
end
| uu____6649 -> begin
(

let uu____6650 = (FStar_TypeChecker_Env.monad_leq env msrc mtgt)
in (match (uu____6650) with
| None -> begin
(

let uu____6652 = (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" (FStar_Ident.text_of_lid msrc) (FStar_Ident.text_of_lid mtgt))
in (failwith uu____6652))
end
| Some ({FStar_TypeChecker_Env.msource = uu____6653; FStar_TypeChecker_Env.mtarget = uu____6654; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____6655; FStar_TypeChecker_Env.mlift_term = None}}) -> begin
(failwith "Impossible : trying to reify a non-reifiable lift (from %s to %s)")
end
| Some ({FStar_TypeChecker_Env.msource = uu____6666; FStar_TypeChecker_Env.mtarget = uu____6667; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____6668; FStar_TypeChecker_Env.mlift_term = Some (lift)}}) -> begin
(

let uu____6686 = (FStar_Syntax_Util.mk_reify e)
in (lift t FStar_Syntax_Syntax.tun uu____6686))
end))
end))
and norm_pattern_args : cfg  ->  env  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun uu____6716 -> (match (uu____6716) with
| (a, imp) -> begin
(

let uu____6723 = (norm cfg env [] a)
in ((uu____6723), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu___162_6738 = comp
in (

let uu____6741 = (

let uu____6742 = (

let uu____6748 = (norm cfg env [] t)
in (

let uu____6749 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____6748), (uu____6749))))
in FStar_Syntax_Syntax.Total (uu____6742))
in {FStar_Syntax_Syntax.n = uu____6741; FStar_Syntax_Syntax.tk = uu___162_6738.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___162_6738.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___162_6738.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu___163_6764 = comp
in (

let uu____6767 = (

let uu____6768 = (

let uu____6774 = (norm cfg env [] t)
in (

let uu____6775 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((uu____6774), (uu____6775))))
in FStar_Syntax_Syntax.GTotal (uu____6768))
in {FStar_Syntax_Syntax.n = uu____6767; FStar_Syntax_Syntax.tk = uu___163_6764.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___163_6764.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___163_6764.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____6806 -> (match (uu____6806) with
| (a, i) -> begin
(

let uu____6813 = (norm cfg env [] a)
in ((uu____6813), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___131_6818 -> (match (uu___131_6818) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____6822 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____6822))
end
| f -> begin
f
end))))
in (

let uu___164_6826 = comp
in (

let uu____6829 = (

let uu____6830 = (

let uu___165_6831 = ct
in (

let uu____6832 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (

let uu____6833 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____6836 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = uu____6832; FStar_Syntax_Syntax.effect_name = uu___165_6831.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____6833; FStar_Syntax_Syntax.effect_args = uu____6836; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (uu____6830))
in {FStar_Syntax_Syntax.n = uu____6829; FStar_Syntax_Syntax.tk = uu___164_6826.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___164_6826.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___164_6826.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let uu___166_6853 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = uu___166_6853.tcenv; delta_level = uu___166_6853.delta_level}) env [] t))
in (

let non_info = (fun t -> (

let uu____6858 = (norm t)
in (FStar_Syntax_Util.non_informative uu____6858)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____6861) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let uu___167_6875 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = uu___167_6875.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___167_6875.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___167_6875.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____6885 = ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ))
in (match (uu____6885) with
| true -> begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let uu___168_6890 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___168_6890.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = uu___168_6890.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___168_6890.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___168_6890.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c)
in (

let uu___169_6892 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___169_6892.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu___169_6892.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___169_6892.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___169_6892.FStar_Syntax_Syntax.flags}))
end)
in (

let uu___170_6893 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = uu___170_6893.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___170_6893.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___170_6893.FStar_Syntax_Syntax.vars}))
end
| uu____6898 -> begin
c
end)))
end
| uu____6899 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env uu____6902 -> (match (uu____6902) with
| (x, imp) -> begin
(

let uu____6905 = (

let uu___171_6906 = x
in (

let uu____6907 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___171_6906.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___171_6906.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6907}))
in ((uu____6905), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let uu____6913 = (FStar_List.fold_left (fun uu____6920 b -> (match (uu____6920) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (uu____6913) with
| (nbs, uu____6937) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
(

let flags = (filter_out_lcomp_cflags lc)
in (

let uu____6954 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____6954) with
| true -> begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____6959 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____6959) with
| true -> begin
(

let uu____6963 = (

let uu____6966 = (

let uu____6967 = (

let uu____6970 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.comp_set_flags uu____6970 flags))
in (FStar_Syntax_Util.lcomp_of_comp uu____6967))
in FStar_Util.Inl (uu____6966))
in Some (uu____6963))
end
| uu____6973 -> begin
(

let uu____6974 = (

let uu____6977 = (

let uu____6978 = (

let uu____6981 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.comp_set_flags uu____6981 flags))
in (FStar_Syntax_Util.lcomp_of_comp uu____6978))
in FStar_Util.Inl (uu____6977))
in Some (uu____6974))
end)))
end
| uu____6984 -> begin
Some (FStar_Util.Inr (((lc.FStar_Syntax_Syntax.eff_name), (flags))))
end)))
end
| uu____6994 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Debug (tm))::stack -> begin
((

let uu____7006 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms")))
in (match (uu____7006) with
| true -> begin
(

let uu____7007 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____7008 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Normalized %s to %s\n" uu____7007 uu____7008)))
end
| uu____7009 -> begin
()
end));
(rebuild cfg env stack t);
)
end
| (Steps (s, dl))::stack -> begin
(rebuild (

let uu___172_7016 = cfg
in {steps = s; tcenv = uu___172_7016.tcenv; delta_level = dl}) env stack t)
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
((set_memo r ((env), (t)));
(log cfg (fun uu____7036 -> (

let uu____7037 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" uu____7037))));
(rebuild cfg env stack t);
)
end
| (Let (env', bs, lb, r))::stack -> begin
(

let body = (FStar_Syntax_Subst.close bs t)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) None r)
in (rebuild cfg env' stack t)))
end
| (Abs (env', bs, env'', lopt, r))::stack -> begin
(

let bs = (norm_binders cfg env' bs)
in (

let lopt = (norm_lcomp_opt cfg env'' lopt)
in (

let uu____7074 = (

let uu___173_7075 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = uu___173_7075.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___173_7075.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___173_7075.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack uu____7074))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, uu____7097), aq, r))::stack -> begin
((log cfg (fun uu____7113 -> (

let uu____7114 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" uu____7114))));
(match ((FStar_List.contains (Exclude (Iota)) cfg.steps)) with
| true -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) None r)
in (rebuild cfg env stack t)))
end
| uu____7121 -> begin
(

let stack = (App (((t), (aq), (r))))::stack
in (norm cfg env stack tm))
end)
end
| uu____7124 -> begin
(

let uu____7125 = (FStar_ST.read m)
in (match (uu____7125) with
| None -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) None r)
in (rebuild cfg env stack t)))
end
| uu____7145 -> begin
(

let stack = (MemoLazy (m))::(App (((t), (aq), (r))))::stack
in (norm cfg env stack tm))
end)
end
| Some (uu____7151, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end))
end);
)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (

let uu____7173 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack uu____7173)))
end
| (Match (env, branches, r))::stack -> begin
((log cfg (fun uu____7180 -> (

let uu____7181 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" uu____7181))));
(

let scrutinee = t
in (

let norm_and_rebuild_match = (fun uu____7186 -> (

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg_exclude_iota_zeta = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun uu___132_7193 -> (match (uu___132_7193) with
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| uu____7194 -> begin
false
end))))
in (

let steps' = (

let uu____7197 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____7197) with
| true -> begin
(Exclude (Zeta))::[]
end
| uu____7199 -> begin
(Exclude (Iota))::(Exclude (Zeta))::[]
end))
in (

let uu___174_7200 = cfg
in {steps = (FStar_List.append steps' cfg.steps); tcenv = uu___174_7200.tcenv; delta_level = new_delta})))
in (

let norm_or_whnf = (fun env t -> (match (whnf) with
| true -> begin
(closure_as_term cfg_exclude_iota_zeta env t)
end
| uu____7210 -> begin
(norm cfg_exclude_iota_zeta env [] t)
end))
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____7234) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let uu____7254 = (norm_pat env hd)
in (match (uu____7254) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (

let uu____7290 = (norm_pat env p)
in (Prims.fst uu____7290)))))
in (((

let uu___175_7302 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = uu___175_7302.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___175_7302.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____7319 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____7353 uu____7354 -> (match (((uu____7353), (uu____7354))) with
| ((pats, env), (p, b)) -> begin
(

let uu____7419 = (norm_pat env p)
in (match (uu____7419) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (uu____7319) with
| (pats, env) -> begin
(((

let uu___176_7485 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = uu___176_7485.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___176_7485.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let uu___177_7499 = x
in (

let uu____7500 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___177_7499.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___177_7499.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7500}))
in (((

let uu___178_7506 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = uu___178_7506.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___178_7506.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let uu___179_7511 = x
in (

let uu____7512 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___179_7511.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___179_7511.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7512}))
in (((

let uu___180_7518 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = uu___180_7518.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___180_7518.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let uu___181_7528 = x
in (

let uu____7529 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___181_7528.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___181_7528.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7529}))
in (

let t = (norm_or_whnf env t)
in (((

let uu___182_7536 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = uu___182_7536.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___182_7536.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| uu____7540 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let uu____7543 = (FStar_Syntax_Subst.open_branch branch)
in (match (uu____7543) with
| (p, wopt, e) -> begin
(

let uu____7561 = (norm_pat env p)
in (match (uu____7561) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____7585 = (norm_or_whnf env w)
in Some (uu____7585))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (

let uu____7590 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) r)
in (rebuild cfg env stack uu____7590))))))))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, uu____7600) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| uu____7611 -> begin
false
end))
in (

let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(

let then_branch = b
in (

let else_branch = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (rest)))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (

let rec matches_pat = (fun scrutinee p -> (

let scrutinee = (FStar_Syntax_Util.unmeta scrutinee)
in (

let uu____7710 = (FStar_Syntax_Util.head_and_args scrutinee)
in (match (uu____7710) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat scrutinee p)
in (match (m) with
| FStar_Util.Inl (uu____7767) -> begin
Some (m)
end
| FStar_Util.Inr (true) -> begin
Some (m)
end
| FStar_Util.Inr (false) -> begin
None
end))))
in (match (mopt) with
| None -> begin
FStar_Util.Inr (false)
end
| Some (m) -> begin
m
end))
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
FStar_Util.Inl ((scrutinee)::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____7798) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| uu____7810 -> begin
(

let uu____7811 = (

let uu____7812 = (is_cons head)
in (not (uu____7812)))
in FStar_Util.Inr (uu____7811))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let uu____7826 = (

let uu____7827 = (FStar_Syntax_Util.un_uinst head)
in uu____7827.FStar_Syntax_Syntax.n)
in (match (uu____7826) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| uu____7834 -> begin
(

let uu____7835 = (

let uu____7836 = (is_cons head)
in (not (uu____7836)))
in FStar_Util.Inr (uu____7835))
end))
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, uu____7870))::rest_a, ((p, uu____7873))::rest_p) -> begin
(

let uu____7901 = (matches_pat t p)
in (match (uu____7901) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____7915 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p, wopt, b))::rest -> begin
(

let uu____7986 = (matches_pat scrutinee p)
in (match (uu____7986) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
((log cfg (fun uu____7996 -> (

let uu____7997 = (FStar_Syntax_Print.pat_to_string p)
in (

let uu____7998 = (

let uu____7999 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right uu____7999 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" uu____7997 uu____7998)))));
(

let env = (FStar_List.fold_left (fun env t -> (

let uu____8008 = (

let uu____8009 = (

let uu____8019 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (uu____8019), (false)))
in Clos (uu____8009))
in (uu____8008)::env)) env s)
in (

let uu____8042 = (guard_when_clause wopt b rest)
in (norm cfg env stack uu____8042)));
)
end))
end))
in (

let uu____8043 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota))))
in (match (uu____8043) with
| true -> begin
(norm_and_rebuild_match ())
end
| uu____8044 -> begin
(matches scrutinee branches)
end))))))));
)
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun uu___133_8057 -> (match (uu___133_8057) with
| UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| Inlining -> begin
(FStar_TypeChecker_Env.Inlining)::[]
end
| uu____8060 -> begin
[]
end))))
in (

let d = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| uu____8064 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d})))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (

let uu____8075 = (config s e)
in (norm uu____8075 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (

let uu____8085 = (config s e)
in (norm_comp uu____8085 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let uu____8092 = (config [] env)
in (norm_universe uu____8092 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (

let uu____8099 = (config [] env)
in (ghost_to_pure_aux uu____8099 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (

let uu____8111 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____8111)))
in (

let uu____8112 = ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ))
in (match (uu____8112) with
| true -> begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let uu___183_8114 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = uu___183_8114.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___183_8114.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____8115 -> (

let uu____8116 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env uu____8116)))})
end
| None -> begin
lc
end)
end
| uu____8117 -> begin
lc
end)))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (

let uu____8124 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string uu____8124)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let uu____8131 = (

let uu____8132 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp uu____8132 [] c))
in (FStar_Syntax_Print.comp_to_string uu____8131)))


let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (

let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (

let rec aux = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(

let uu____8169 = (

let uu____8170 = (

let uu____8175 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (uu____8175)))
in FStar_Syntax_Syntax.Tm_refine (uu____8170))
in (mk uu____8169 t0.FStar_Syntax_Syntax.pos))
end
| uu____8180 -> begin
t
end))
end
| uu____8181 -> begin
t
end)))
in (aux t))))


let eta_expand_with_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun t sort -> (

let uu____8188 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (uu____8188) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| uu____8204 -> begin
(

let uu____8208 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (uu____8208) with
| (binders, args) -> begin
(

let uu____8218 = ((FStar_Syntax_Syntax.mk_Tm_app t args) None t.FStar_Syntax_Syntax.pos)
in (

let uu____8223 = (

let uu____8230 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_39 -> FStar_Util.Inl (_0_39)))
in (FStar_All.pipe_right uu____8230 (fun _0_40 -> Some (_0_40))))
in (FStar_Syntax_Util.abs binders uu____8218 uu____8223)))
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____8266 = (

let uu____8270 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((uu____8270), (t.FStar_Syntax_Syntax.n)))
in (match (uu____8266) with
| (Some (sort), uu____8277) -> begin
(

let uu____8279 = (mk sort t.FStar_Syntax_Syntax.pos)
in (eta_expand_with_type t uu____8279))
end
| (uu____8280, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(eta_expand_with_type t x.FStar_Syntax_Syntax.sort)
end
| uu____8284 -> begin
(

let uu____8288 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____8288) with
| (head, args) -> begin
(

let uu____8314 = (

let uu____8315 = (FStar_Syntax_Subst.compress head)
in uu____8315.FStar_Syntax_Syntax.n)
in (match (uu____8314) with
| FStar_Syntax_Syntax.Tm_uvar (uu____8318, thead) -> begin
(

let uu____8332 = (FStar_Syntax_Util.arrow_formals thead)
in (match (uu____8332) with
| (formals, tres) -> begin
(match (((FStar_List.length formals) = (FStar_List.length args))) with
| true -> begin
t
end
| uu____8362 -> begin
(

let uu____8363 = (env.FStar_TypeChecker_Env.type_of (

let uu___184_8367 = env
in {FStar_TypeChecker_Env.solver = uu___184_8367.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___184_8367.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___184_8367.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___184_8367.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___184_8367.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___184_8367.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = uu___184_8367.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___184_8367.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___184_8367.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___184_8367.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___184_8367.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___184_8367.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___184_8367.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___184_8367.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___184_8367.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___184_8367.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___184_8367.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___184_8367.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___184_8367.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___184_8367.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___184_8367.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (uu____8363) with
| (uu____8368, ty, uu____8370) -> begin
(eta_expand_with_type t ty)
end))
end)
end))
end
| uu____8371 -> begin
(

let uu____8372 = (env.FStar_TypeChecker_Env.type_of (

let uu___185_8376 = env
in {FStar_TypeChecker_Env.solver = uu___185_8376.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___185_8376.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___185_8376.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___185_8376.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___185_8376.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___185_8376.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = uu___185_8376.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___185_8376.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___185_8376.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___185_8376.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___185_8376.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___185_8376.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___185_8376.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___185_8376.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___185_8376.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___185_8376.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___185_8376.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___185_8376.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___185_8376.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___185_8376.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___185_8376.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (uu____8372) with
| (uu____8377, ty, uu____8379) -> begin
(eta_expand_with_type t ty)
end))
end))
end))
end)))




