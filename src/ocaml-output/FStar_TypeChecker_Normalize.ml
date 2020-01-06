
open Prims
open FStar_Pervasives

let cases : 'Auu____10 'Auu____11 . ('Auu____10  ->  'Auu____11)  ->  'Auu____11  ->  'Auu____10 FStar_Pervasives_Native.option  ->  'Auu____11 = (fun f d uu___0_31 -> (match (uu___0_31) with
| FStar_Pervasives_Native.Some (x) -> begin
(f x)
end
| FStar_Pervasives_Native.None -> begin
d
end))

type closure =
| Clos of ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
| Univ of FStar_Syntax_Syntax.universe
| Dummy


let uu___is_Clos : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Clos (_0) -> begin
true
end
| uu____129 -> begin
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
| uu____241 -> begin
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
| uu____259 -> begin
false
end))


type env =
(FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list


let dummy : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) = ((FStar_Pervasives_Native.None), (Dummy))


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list

type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option * FStar_Range.range)
| App of (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)
| Let of (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range)
| Cfg of FStar_TypeChecker_Cfg.cfg
| Debug of (FStar_Syntax_Syntax.term * FStar_Util.time)


let uu___is_Arg : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Arg (_0) -> begin
true
end
| uu____428 -> begin
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
| uu____471 -> begin
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
| uu____514 -> begin
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
| uu____559 -> begin
false
end))


let __proj__Match__item___0 : stack_elt  ->  (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Match (_0) -> begin
_0
end))


let uu___is_Abs : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Abs (_0) -> begin
true
end
| uu____614 -> begin
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
| uu____677 -> begin
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
| uu____726 -> begin
false
end))


let __proj__Meta__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.metadata * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
_0
end))


let uu___is_Let : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
true
end
| uu____771 -> begin
false
end))


let __proj__Let__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
_0
end))


let uu___is_Cfg : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cfg (_0) -> begin
true
end
| uu____814 -> begin
false
end))


let __proj__Cfg__item___0 : stack_elt  ->  FStar_TypeChecker_Cfg.cfg = (fun projectee -> (match (projectee) with
| Cfg (_0) -> begin
_0
end))


let uu___is_Debug : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
true
end
| uu____837 -> begin
false
end))


let __proj__Debug__item___0 : stack_elt  ->  (FStar_Syntax_Syntax.term * FStar_Util.time) = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
_0
end))


type stack =
stack_elt Prims.list


let head_of : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____866 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____866) with
| (hd1, uu____882) -> begin
hd1
end)))


let mk : 'Auu____910 . 'Auu____910  ->  FStar_Range.range  ->  'Auu____910 FStar_Syntax_Syntax.syntax = (fun t r -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r))


let set_memo : 'a . FStar_TypeChecker_Cfg.cfg  ->  'a FStar_Syntax_Syntax.memo  ->  'a  ->  unit = (fun cfg r t -> (match (cfg.FStar_TypeChecker_Cfg.memoize_lazy) with
| true -> begin
(

let uu____953 = (FStar_ST.op_Bang r)
in (match (uu____953) with
| FStar_Pervasives_Native.Some (uu____979) -> begin
(failwith "Unexpected set_memo: thunk already evaluated")
end
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some (t)))
end))
end
| uu____1004 -> begin
()
end))


let closure_to_string : closure  ->  Prims.string = (fun uu___1_1012 -> (match (uu___1_1012) with
| Clos (env, t, uu____1016, uu____1017) -> begin
(

let uu____1064 = (FStar_All.pipe_right (FStar_List.length env) FStar_Util.string_of_int)
in (

let uu____1074 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "(env=%s elts; %s)" uu____1064 uu____1074)))
end
| Univ (uu____1077) -> begin
"Univ"
end
| Dummy -> begin
"dummy"
end))


let env_to_string : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list  ->  Prims.string = (fun env -> (

let uu____1103 = (FStar_List.map (fun uu____1119 -> (match (uu____1119) with
| (bopt, c) -> begin
(

let uu____1133 = (match (bopt) with
| FStar_Pervasives_Native.None -> begin
"."
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.binder_to_string x)
end)
in (

let uu____1138 = (closure_to_string c)
in (FStar_Util.format2 "(%s, %s)" uu____1133 uu____1138)))
end)) env)
in (FStar_All.pipe_right uu____1103 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun uu___2_1152 -> (match (uu___2_1152) with
| Arg (c, uu____1155, uu____1156) -> begin
(

let uu____1157 = (closure_to_string c)
in (FStar_Util.format1 "Closure %s" uu____1157))
end
| MemoLazy (uu____1160) -> begin
"MemoLazy"
end
| Abs (uu____1168, bs, uu____1170, uu____1171, uu____1172) -> begin
(

let uu____1177 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" uu____1177))
end
| UnivArgs (uu____1188) -> begin
"UnivArgs"
end
| Match (uu____1196) -> begin
"Match"
end
| App (uu____1206, t, uu____1208, uu____1209) -> begin
(

let uu____1210 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "App %s" uu____1210))
end
| Meta (uu____1213, m, uu____1215) -> begin
"Meta"
end
| Let (uu____1217) -> begin
"Let"
end
| Cfg (uu____1227) -> begin
"Cfg"
end
| Debug (t, uu____1230) -> begin
(

let uu____1231 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Debug %s" uu____1231))
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (

let uu____1245 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right uu____1245 (FStar_String.concat "; "))))


let is_empty : 'Auu____1260 . 'Auu____1260 Prims.list  ->  Prims.bool = (fun uu___3_1268 -> (match (uu___3_1268) with
| [] -> begin
true
end
| uu____1272 -> begin
false
end))


let lookup_bvar : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.bv  ->  closure = (fun env x -> (FStar_All.try_with (fun uu___114_1305 -> (match (()) with
| () -> begin
(

let uu____1306 = (FStar_List.nth env x.FStar_Syntax_Syntax.index)
in (FStar_Pervasives_Native.snd uu____1306))
end)) (fun uu___113_1323 -> (

let uu____1324 = (

let uu____1326 = (FStar_Syntax_Print.db_to_string x)
in (

let uu____1328 = (env_to_string env)
in (FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1326 uu____1328)))
in (failwith uu____1324)))))


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun l -> (

let uu____1339 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid)
in (match (uu____1339) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Pure_lid)
end
| uu____1344 -> begin
(

let uu____1346 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid)
in (match (uu____1346) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Tot_lid)
end
| uu____1351 -> begin
(

let uu____1353 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid)
in (match (uu____1353) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_PURE_lid)
end
| uu____1358 -> begin
FStar_Pervasives_Native.None
end))
end))
end)))


let norm_universe : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us1 = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let uu____1391 = (FStar_List.fold_left (fun uu____1417 u1 -> (match (uu____1417) with
| (cur_kernel, cur_max, out) -> begin
(

let uu____1442 = (FStar_Syntax_Util.univ_kernel u1)
in (match (uu____1442) with
| (k_u, n1) -> begin
(

let uu____1460 = (FStar_Syntax_Util.eq_univs cur_kernel k_u)
in (match (uu____1460) with
| true -> begin
((cur_kernel), (u1), (out))
end
| uu____1473 -> begin
((k_u), (u1), ((cur_max)::out))
end))
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us1)
in (match (uu____1391) with
| (uu____1481, u1, out) -> begin
(FStar_List.rev ((u1)::out))
end))))
in (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(FStar_All.try_with (fun uu___148_1507 -> (match (()) with
| () -> begin
(

let uu____1510 = (

let uu____1511 = (FStar_List.nth env x)
in (FStar_Pervasives_Native.snd uu____1511))
in (match (uu____1510) with
| Univ (u3) -> begin
((

let uu____1530 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv) (FStar_Options.Other ("univ_norm")))
in (match (uu____1530) with
| true -> begin
(

let uu____1535 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.print1 "Univ (in norm_universe): %s\n" uu____1535))
end
| uu____1538 -> begin
()
end));
(aux u3);
)
end
| Dummy -> begin
(u2)::[]
end
| uu____1540 -> begin
(

let uu____1541 = (

let uu____1543 = (FStar_Util.string_of_int x)
in (FStar_Util.format1 "Impossible: universe variable u@%s bound to a term" uu____1543))
in (failwith uu____1541))
end))
end)) (fun uu___147_1550 -> (match (uu___147_1550) with
| uu____1553 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.allow_unbound_universes) with
| true -> begin
(FStar_Syntax_Syntax.U_unknown)::[]
end
| uu____1557 -> begin
(

let uu____1559 = (

let uu____1561 = (FStar_Util.string_of_int x)
in (FStar_String.op_Hat "Universe variable not found: u@" uu____1561))
in (failwith uu____1559))
end)
end)))
end
| FStar_Syntax_Syntax.U_unif (uu____1566) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_zero -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_unif (uu____1575) -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_name (uu____1584) -> begin
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

let uu____1591 = (FStar_List.collect aux us)
in (FStar_All.pipe_right uu____1591 norm_univs))
in (match (us1) with
| (u_k)::(hd1)::rest -> begin
(

let rest1 = (hd1)::rest
in (

let uu____1608 = (FStar_Syntax_Util.univ_kernel u_k)
in (match (uu____1608) with
| (FStar_Syntax_Syntax.U_zero, n1) -> begin
(

let uu____1619 = (FStar_All.pipe_right rest1 (FStar_List.for_all (fun u3 -> (

let uu____1629 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____1629) with
| (uu____1636, m) -> begin
(n1 <= m)
end)))))
in (match (uu____1619) with
| true -> begin
rest1
end
| uu____1643 -> begin
us1
end))
end
| uu____1645 -> begin
us1
end)))
end
| uu____1651 -> begin
us1
end))
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1655 = (aux u3)
in (FStar_List.map (fun _1658 -> FStar_Syntax_Syntax.U_succ (_1658)) uu____1655))
end)))
in (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.erase_universes) with
| true -> begin
FStar_Syntax_Syntax.U_unknown
end
| uu____1660 -> begin
(

let uu____1662 = (aux u)
in (match (uu____1662) with
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
end))))


let rec inline_closure_env : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env stack t -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____1823 -> (

let uu____1824 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1826 = (env_to_string env)
in (

let uu____1828 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n" uu____1824 uu____1826 uu____1828))))));
(match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars) -> begin
(rebuild_closure cfg env stack t)
end
| uu____1841 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1844) -> begin
(

let uu____1867 = (FStar_Syntax_Subst.compress t)
in (inline_closure_env cfg env stack uu____1867))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1868) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_name (uu____1869) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_lazy (uu____1870) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1871) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_uvar (uv, s) -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____1896) -> begin
(

let uu____1909 = (

let uu____1911 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____1913 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s): CheckNoUvars: Unexpected unification variable remains: %s" uu____1911 uu____1913)))
in (failwith uu____1909))
end
| uu____1918 -> begin
(inline_closure_env cfg env stack t1)
end))
end
| uu____1919 -> begin
(

let s' = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (fun s1 -> (FStar_All.pipe_right s1 (FStar_List.map (fun uu___4_1954 -> (match (uu___4_1954) with
| FStar_Syntax_Syntax.NT (x, t1) -> begin
(

let uu____1961 = (

let uu____1968 = (inline_closure_env cfg env [] t1)
in ((x), (uu____1968)))
in FStar_Syntax_Syntax.NT (uu____1961))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let x_i = (FStar_Syntax_Syntax.bv_to_tm (

let uu___242_1980 = x
in {FStar_Syntax_Syntax.ppname = uu___242_1980.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___242_1980.FStar_Syntax_Syntax.sort}))
in (

let t1 = (inline_closure_env cfg env [] x_i)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x_j) -> begin
FStar_Syntax_Syntax.NM (((x), (x_j.FStar_Syntax_Syntax.index)))
end
| uu____1986 -> begin
FStar_Syntax_Syntax.NT (((x), (t1)))
end)))
end
| uu____1989 -> begin
(failwith "Impossible: subst invariant of uvar nodes")
end)))))))
in (

let t1 = (

let uu___251_1994 = t
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (((uv), (((s'), ((FStar_Pervasives_Native.snd s)))))); FStar_Syntax_Syntax.pos = uu___251_1994.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___251_1994.FStar_Syntax_Syntax.vars})
in (rebuild_closure cfg env stack t1)))
end)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let t1 = (

let uu____2015 = (

let uu____2016 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (uu____2016))
in (mk uu____2015 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env stack t1))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let t1 = (

let uu____2024 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2024))
in (rebuild_closure cfg env stack t1))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____2026 = (lookup_bvar env x)
in (match (uu____2026) with
| Univ (uu____2029) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(

let x1 = (

let uu___267_2034 = x
in {FStar_Syntax_Syntax.ppname = uu___267_2034.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___267_2034.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun})
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_bvar (x1)) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env stack t1)))
end
| Clos (env1, t0, uu____2040, uu____2041) -> begin
(inline_closure_env cfg env1 stack t0)
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____2132 stack1 -> (match (uu____2132) with
| (a, aq) -> begin
(

let uu____2144 = (

let uu____2145 = (

let uu____2152 = (

let uu____2153 = (

let uu____2185 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____2185), (false)))
in Clos (uu____2153))
in ((uu____2152), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (uu____2145))
in (uu____2144)::stack1)
end)) args))
in (inline_closure_env cfg env stack1 head1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let env' = (FStar_All.pipe_right env (FStar_List.fold_right (fun _b env1 -> (((FStar_Pervasives_Native.None), (Dummy)))::env1) bs))
in (

let stack1 = (Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack
in (inline_closure_env cfg env' stack1 body)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____2353 = (close_binders cfg env bs)
in (match (uu____2353) with
| (bs1, env') -> begin
(

let c1 = (close_comp cfg env' c)
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_arrow (((bs1), (c1)))) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env stack t1)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____2403) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.for_extraction -> begin
(inline_closure_env cfg env stack x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____2414 = (

let uu____2427 = (

let uu____2436 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2436)::[])
in (close_binders cfg env uu____2427))
in (match (uu____2414) with
| (x1, env1) -> begin
(

let phi1 = (non_tail_inline_closure_env cfg env1 phi)
in (

let t1 = (

let uu____2481 = (

let uu____2482 = (

let uu____2489 = (

let uu____2490 = (FStar_List.hd x1)
in (FStar_All.pipe_right uu____2490 FStar_Pervasives_Native.fst))
in ((uu____2489), (phi1)))
in FStar_Syntax_Syntax.Tm_refine (uu____2482))
in (mk uu____2481 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env1 stack t1)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, (annot, tacopt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____2589 = (non_tail_inline_closure_env cfg env t2)
in FStar_Util.Inl (uu____2589))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2603 = (close_comp cfg env c)
in FStar_Util.Inr (uu____2603))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (non_tail_inline_closure_env cfg env))
in (

let t2 = (

let uu____2622 = (

let uu____2623 = (

let uu____2650 = (non_tail_inline_closure_env cfg env t1)
in ((uu____2650), (((annot1), (tacopt1))), (lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2623))
in (mk uu____2622 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env stack t2))))
end
| FStar_Syntax_Syntax.Tm_quoted (t', qi) -> begin
(

let t1 = (match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____2696 = (

let uu____2697 = (

let uu____2704 = (non_tail_inline_closure_env cfg env t')
in ((uu____2704), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____2697))
in (mk uu____2696 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted (non_tail_inline_closure_env cfg env) qi)
in (mk (FStar_Syntax_Syntax.Tm_quoted (((t'), (qi1)))) t.FStar_Syntax_Syntax.pos))
end)
in (rebuild_closure cfg env stack t1))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(

let stack1 = (Meta (((env), (m), (t.FStar_Syntax_Syntax.pos))))::stack
in (inline_closure_env cfg env stack1 t'))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env1 = (FStar_List.fold_left (fun env1 uu____2759 -> (dummy)::env1) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (non_tail_inline_closure_env cfg env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (non_tail_inline_closure_env cfg env1 lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____2780 = (

let uu____2791 = (FStar_Syntax_Syntax.is_top_level ((lb)::[]))
in (match (uu____2791) with
| true -> begin
((lb.FStar_Syntax_Syntax.lbname), (body))
end
| uu____2810 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2813 = (non_tail_inline_closure_env cfg ((dummy)::env0) body)
in ((FStar_Util.Inl ((

let uu___359_2829 = x
in {FStar_Syntax_Syntax.ppname = uu___359_2829.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___359_2829.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = typ}))), (uu____2813))))
end))
in (match (uu____2780) with
| (nm, body1) -> begin
(

let lb1 = (

let uu___364_2847 = lb
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___364_2847.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = uu___364_2847.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___364_2847.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___364_2847.FStar_Syntax_Syntax.lbpos})
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (body1)))) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env0 stack t1)))
end))))))
end
| FStar_Syntax_Syntax.Tm_let ((uu____2864, lbs), body) -> begin
(

let norm_one_lb = (fun env1 lb -> (

let env_univs = (FStar_List.fold_right (fun uu____2930 env2 -> (dummy)::env2) lb.FStar_Syntax_Syntax.lbunivs env1)
in (

let env2 = (

let uu____2947 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____2947) with
| true -> begin
env_univs
end
| uu____2950 -> begin
(FStar_List.fold_right (fun uu____2962 env2 -> (dummy)::env2) lbs env_univs)
end))
in (

let ty = (non_tail_inline_closure_env cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (

let nm = (

let uu____2986 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____2986) with
| true -> begin
lb.FStar_Syntax_Syntax.lbname
end
| uu____2993 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in FStar_Util.Inl ((

let uu___387_2997 = x
in {FStar_Syntax_Syntax.ppname = uu___387_2997.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___387_2997.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
end))
in (

let uu___390_2998 = lb
in (

let uu____2999 = (non_tail_inline_closure_env cfg env2 lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___390_2998.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___390_2998.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____2999; FStar_Syntax_Syntax.lbattrs = uu___390_2998.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___390_2998.FStar_Syntax_Syntax.lbpos})))))))
in (

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body1 = (

let body_env = (FStar_List.fold_right (fun uu____3031 env1 -> (dummy)::env1) lbs1 env)
in (non_tail_inline_closure_env cfg body_env body))
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs1))), (body1)))) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env stack t1)))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let stack1 = (Match (((env), (branches), (cfg), (t.FStar_Syntax_Syntax.pos))))::stack
in (inline_closure_env cfg env stack1 head1))
end)
end);
))
and non_tail_inline_closure_env : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env t -> (inline_closure_env cfg env [] t))
and rebuild_closure : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env stack t -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____3123 -> (

let uu____3124 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____3126 = (env_to_string env)
in (

let uu____3128 = (stack_to_string stack)
in (

let uu____3130 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print4 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n" uu____3124 uu____3126 uu____3128 uu____3130)))))));
(match (stack) with
| [] -> begin
t
end
| (Arg (Clos (env_arg, tm, uu____3137, uu____3138), aq, r))::stack1 -> begin
(

let stack2 = (App (((env), (t), (aq), (r))))::stack1
in (inline_closure_env cfg env_arg stack2 tm))
end
| (App (env1, head1, aq, r))::stack1 -> begin
(

let t1 = (FStar_Syntax_Syntax.extend_app head1 ((t), (aq)) FStar_Pervasives_Native.None r)
in (rebuild_closure cfg env1 stack1 t1))
end
| (Abs (env', bs, env'', lopt, r))::stack1 -> begin
(

let uu____3219 = (close_binders cfg env' bs)
in (match (uu____3219) with
| (bs1, uu____3235) -> begin
(

let lopt1 = (close_lcomp_opt cfg env'' lopt)
in (

let uu____3255 = (

let uu___448_3258 = (FStar_Syntax_Util.abs bs1 t lopt1)
in {FStar_Syntax_Syntax.n = uu___448_3258.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___448_3258.FStar_Syntax_Syntax.vars})
in (rebuild_closure cfg env stack1 uu____3255)))
end))
end
| (Match (env1, branches, cfg1, r))::stack1 -> begin
(

let close_one_branch = (fun env2 uu____3314 -> (match (uu____3314) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env3 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____3429) -> begin
((p), (env3))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3460 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____3549 uu____3550 -> (match (((uu____3549), (uu____3550))) with
| ((pats1, env4), (p1, b)) -> begin
(

let uu____3700 = (norm_pat env4 p1)
in (match (uu____3700) with
| (p2, env5) -> begin
(((((p2), (b)))::pats1), (env5))
end))
end)) (([]), (env3))))
in (match (uu____3460) with
| (pats1, env4) -> begin
(((

let uu___485_3870 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___485_3870.FStar_Syntax_Syntax.p})), (env4))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___489_3891 = x
in (

let uu____3892 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___489_3891.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___489_3891.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3892}))
in (((

let uu___492_3906 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___492_3906.FStar_Syntax_Syntax.p})), ((dummy)::env3)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___496_3917 = x
in (

let uu____3918 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___496_3917.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___496_3917.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3918}))
in (((

let uu___499_3932 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___499_3932.FStar_Syntax_Syntax.p})), ((dummy)::env3)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t1) -> begin
(

let x1 = (

let uu___505_3948 = x
in (

let uu____3949 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___505_3948.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___505_3948.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3949}))
in (

let t2 = (non_tail_inline_closure_env cfg1 env3 t1)
in (((

let uu___509_3966 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t2))); FStar_Syntax_Syntax.p = uu___509_3966.FStar_Syntax_Syntax.p})), (env3))))
end))
in (

let uu____3971 = (norm_pat env2 pat)
in (match (uu____3971) with
| (pat1, env3) -> begin
(

let w_opt1 = (match (w_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____4040 = (non_tail_inline_closure_env cfg1 env3 w)
in FStar_Pervasives_Native.Some (uu____4040))
end)
in (

let tm1 = (non_tail_inline_closure_env cfg1 env3 tm)
in ((pat1), (w_opt1), (tm1))))
end)))
end))
in (

let t1 = (

let uu____4059 = (

let uu____4060 = (

let uu____4083 = (FStar_All.pipe_right branches (FStar_List.map (close_one_branch env1)))
in ((t), (uu____4083)))
in FStar_Syntax_Syntax.Tm_match (uu____4060))
in (mk uu____4059 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg1 env1 stack1 t1)))
end
| (Meta (env_m, m, r))::stack1 -> begin
(

let m1 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (names1, args) -> begin
(

let uu____4219 = (

let uu____4240 = (FStar_All.pipe_right names1 (FStar_List.map (non_tail_inline_closure_env cfg env_m)))
in (

let uu____4257 = (FStar_All.pipe_right args (FStar_List.map (fun args1 -> (FStar_All.pipe_right args1 (FStar_List.map (fun uu____4366 -> (match (uu____4366) with
| (a, q) -> begin
(

let uu____4393 = (non_tail_inline_closure_env cfg env_m a)
in ((uu____4393), (q)))
end)))))))
in ((uu____4240), (uu____4257))))
in FStar_Syntax_Syntax.Meta_pattern (uu____4219))
end
| FStar_Syntax_Syntax.Meta_monadic (m1, tbody) -> begin
(

let uu____4422 = (

let uu____4429 = (non_tail_inline_closure_env cfg env_m tbody)
in ((m1), (uu____4429)))
in FStar_Syntax_Syntax.Meta_monadic (uu____4422))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody) -> begin
(

let uu____4441 = (

let uu____4450 = (non_tail_inline_closure_env cfg env_m tbody)
in ((m1), (m2), (uu____4450)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____4441))
end
| uu____4455 -> begin
m
end)
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m1)))) r)
in (rebuild_closure cfg env stack1 t1)))
end
| uu____4461 -> begin
(failwith "Impossible: unexpected stack element")
end);
))
and close_imp : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun cfg env imp -> (match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____4477 = (

let uu____4478 = (inline_closure_env cfg env [] t)
in FStar_Syntax_Syntax.Meta (uu____4478))
in FStar_Pervasives_Native.Some (uu____4477))
end
| i -> begin
i
end))
and close_binders : FStar_TypeChecker_Cfg.cfg  ->  env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * env) = (fun cfg env bs -> (

let uu____4495 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____4579 uu____4580 -> (match (((uu____4579), (uu____4580))) with
| ((env1, out), (b, imp)) -> begin
(

let b1 = (

let uu___564_4720 = b
in (

let uu____4721 = (inline_closure_env cfg env1 [] b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___564_4720.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___564_4720.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4721}))
in (

let imp1 = (close_imp cfg env1 imp)
in (

let env2 = (dummy)::env1
in ((env2), ((((b1), (imp1)))::out)))))
end)) ((env), ([]))))
in (match (uu____4495) with
| (env1, bs1) -> begin
(((FStar_List.rev bs1)), (env1))
end)))
and close_comp : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars) -> begin
c
end
| uu____4863 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____4876 = (inline_closure_env cfg env [] t)
in (

let uu____4877 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____4876 uu____4877)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____4890 = (inline_closure_env cfg env [] t)
in (

let uu____4891 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____4890 uu____4891)))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let rt = (inline_closure_env cfg env [] c1.FStar_Syntax_Syntax.result_typ)
in (

let args = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun uu____4945 -> (match (uu____4945) with
| (a, q) -> begin
(

let uu____4966 = (inline_closure_env cfg env [] a)
in ((uu____4966), (q)))
end))))
in (

let flags = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___5_4983 -> (match (uu___5_4983) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____4987 = (inline_closure_env cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____4987))
end
| f -> begin
f
end))))
in (

let uu____4991 = (

let uu___597_4992 = c1
in (

let uu____4993 = (FStar_List.map (norm_universe cfg env) c1.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = uu____4993; FStar_Syntax_Syntax.effect_name = uu___597_4992.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp uu____4991)))))
end)
end))
and close_lcomp_opt : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.filter (fun uu___6_5011 -> (match (uu___6_5011) with
| FStar_Syntax_Syntax.DECREASES (uu____5013) -> begin
false
end
| uu____5017 -> begin
true
end))))
in (

let rc1 = (

let uu___609_5020 = rc
in (

let uu____5021 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inline_closure_env cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___609_5020.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____5021; FStar_Syntax_Syntax.residual_flags = flags}))
in FStar_Pervasives_Native.Some (rc1)))
end
| uu____5030 -> begin
lopt
end))


let filter_out_lcomp_cflags : FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun flags -> (FStar_All.pipe_right flags (FStar_List.filter (fun uu___7_5051 -> (match (uu___7_5051) with
| FStar_Syntax_Syntax.DECREASES (uu____5053) -> begin
false
end
| uu____5057 -> begin
true
end)))))


let closure_as_term : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (non_tail_inline_closure_env cfg env t))


let unembed_binder_knot : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let unembed_binder : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option = (fun t -> (

let uu____5104 = (FStar_ST.op_Bang unembed_binder_knot)
in (match (uu____5104) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____5143 = (FStar_Syntax_Embeddings.unembed e t)
in (uu____5143 true FStar_Syntax_Embeddings.id_norm_cb))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_UnembedBinderKnot), ("unembed_binder_knot is unset!")));
FStar_Pervasives_Native.None;
)
end)))


let mk_psc_subst : 'Auu____5163 . FStar_TypeChecker_Cfg.cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____5163) FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun cfg env -> (FStar_List.fold_right (fun uu____5225 subst1 -> (match (uu____5225) with
| (binder_opt, closure) -> begin
(match (((binder_opt), (closure))) with
| (FStar_Pervasives_Native.Some (b), Clos (env1, term, uu____5266, uu____5267)) -> begin
(

let uu____5328 = b
in (match (uu____5328) with
| (bv, uu____5336) -> begin
(

let uu____5337 = (

let uu____5339 = (FStar_Syntax_Util.is_constructed_typ bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.binder_lid)
in (not (uu____5339)))
in (match (uu____5337) with
| true -> begin
subst1
end
| uu____5344 -> begin
(

let term1 = (closure_as_term cfg env1 term)
in (

let uu____5347 = (unembed_binder term1)
in (match (uu____5347) with
| FStar_Pervasives_Native.None -> begin
subst1
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let b1 = (

let uu____5354 = (

let uu___649_5355 = bv
in (

let uu____5356 = (FStar_Syntax_Subst.subst subst1 (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___649_5355.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___649_5355.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5356}))
in (FStar_Syntax_Syntax.freshen_bv uu____5354))
in (

let b_for_x = (

let uu____5362 = (

let uu____5369 = (FStar_Syntax_Syntax.bv_to_name b1)
in (((FStar_Pervasives_Native.fst x)), (uu____5369)))
in FStar_Syntax_Syntax.NT (uu____5362))
in (

let subst2 = (FStar_List.filter (fun uu___8_5385 -> (match (uu___8_5385) with
| FStar_Syntax_Syntax.NT (uu____5387, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (b'); FStar_Syntax_Syntax.pos = uu____5389; FStar_Syntax_Syntax.vars = uu____5390}) -> begin
(

let uu____5395 = (FStar_Ident.ident_equals b1.FStar_Syntax_Syntax.ppname b'.FStar_Syntax_Syntax.ppname)
in (not (uu____5395)))
end
| uu____5397 -> begin
true
end)) subst1)
in (b_for_x)::subst2)))
end)))
end))
end))
end
| uu____5399 -> begin
subst1
end)
end)) env []))


let reduce_primops : 'Auu____5421 . FStar_Syntax_Embeddings.norm_cb  ->  FStar_TypeChecker_Cfg.cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____5421) FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun norm_cb cfg env tm -> (match ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.primops))) with
| true -> begin
tm
end
| uu____5471 -> begin
(

let uu____5473 = (FStar_Syntax_Util.head_and_args tm)
in (match (uu____5473) with
| (head1, args) -> begin
(

let uu____5518 = (

let uu____5519 = (FStar_Syntax_Util.un_uinst head1)
in uu____5519.FStar_Syntax_Syntax.n)
in (match (uu____5518) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5525 = (FStar_TypeChecker_Cfg.find_prim_step cfg fv)
in (match (uu____5525) with
| FStar_Pervasives_Native.Some (prim_step) when (prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok || (not (cfg.FStar_TypeChecker_Cfg.strong))) -> begin
(

let l = (FStar_List.length args)
in (match ((l < prim_step.FStar_TypeChecker_Cfg.arity)) with
| true -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5548 -> (

let uu____5549 = (FStar_Syntax_Print.lid_to_string prim_step.FStar_TypeChecker_Cfg.name)
in (

let uu____5551 = (FStar_Util.string_of_int l)
in (

let uu____5553 = (FStar_Util.string_of_int prim_step.FStar_TypeChecker_Cfg.arity)
in (FStar_Util.print3 "primop: found partially applied %s (%s/%s args)\n" uu____5549 uu____5551 uu____5553))))));
tm;
)
end
| uu____5556 -> begin
(

let uu____5558 = (match ((Prims.op_Equality l prim_step.FStar_TypeChecker_Cfg.arity)) with
| true -> begin
((args), ([]))
end
| uu____5607 -> begin
(FStar_List.splitAt prim_step.FStar_TypeChecker_Cfg.arity args)
end)
in (match (uu____5558) with
| (args_1, args_2) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5644 -> (

let uu____5645 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: trying to reduce <%s>\n" uu____5645))));
(

let psc = {FStar_TypeChecker_Cfg.psc_range = head1.FStar_Syntax_Syntax.pos; FStar_TypeChecker_Cfg.psc_subst = (fun uu____5650 -> (match (prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution) with
| true -> begin
(mk_psc_subst cfg env)
end
| uu____5652 -> begin
[]
end))}
in (

let r = (prim_step.FStar_TypeChecker_Cfg.interpretation psc norm_cb args_1)
in (match (r) with
| FStar_Pervasives_Native.None -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5664 -> (

let uu____5665 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: <%s> did not reduce\n" uu____5665))));
tm;
)
end
| FStar_Pervasives_Native.Some (reduced) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5673 -> (

let uu____5674 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____5676 = (FStar_Syntax_Print.term_to_string reduced)
in (FStar_Util.print2 "primop: <%s> reduced to <%s>\n" uu____5674 uu____5676)))));
(FStar_Syntax_Util.mk_app reduced args_2);
)
end)));
)
end))
end))
end
| FStar_Pervasives_Native.Some (uu____5679) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5683 -> (

let uu____5684 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: not reducing <%s> since we\'re doing strong reduction\n" uu____5684))));
tm;
)
end
| FStar_Pervasives_Native.None -> begin
tm
end))
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of) when (not (cfg.FStar_TypeChecker_Cfg.strong)) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5690 -> (

let uu____5691 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: reducing <%s>\n" uu____5691))));
(match (args) with
| ((a1, uu____5697))::[] -> begin
(FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range a1.FStar_Syntax_Syntax.pos tm.FStar_Syntax_Syntax.pos)
end
| uu____5722 -> begin
tm
end);
)
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of) when (not (cfg.FStar_TypeChecker_Cfg.strong)) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5736 -> (

let uu____5737 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: reducing <%s>\n" uu____5737))));
(match (args) with
| ((t, uu____5743))::((r, uu____5745))::[] -> begin
(

let uu____5786 = (FStar_TypeChecker_Cfg.try_unembed_simple FStar_Syntax_Embeddings.e_range r)
in (match (uu____5786) with
| FStar_Pervasives_Native.Some (rng) -> begin
(FStar_Syntax_Subst.set_use_range rng t)
end
| FStar_Pervasives_Native.None -> begin
tm
end))
end
| uu____5792 -> begin
tm
end);
)
end
| uu____5803 -> begin
tm
end))
end))
end))


let reduce_equality : 'Auu____5814 . FStar_Syntax_Embeddings.norm_cb  ->  FStar_TypeChecker_Cfg.cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____5814) FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun norm_cb cfg tm -> (reduce_primops norm_cb (

let uu___737_5863 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___739_5866 = FStar_TypeChecker_Cfg.default_steps
in {FStar_TypeChecker_Cfg.beta = uu___739_5866.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___739_5866.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___739_5866.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___739_5866.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___739_5866.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = true; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___739_5866.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___739_5866.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___739_5866.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___739_5866.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___739_5866.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___739_5866.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___739_5866.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___739_5866.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___739_5866.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___739_5866.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___739_5866.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___739_5866.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___739_5866.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___739_5866.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___739_5866.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___739_5866.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___739_5866.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___739_5866.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___739_5866.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___739_5866.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___737_5863.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___737_5863.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___737_5863.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = FStar_TypeChecker_Cfg.equality_ops; FStar_TypeChecker_Cfg.strong = uu___737_5863.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___737_5863.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___737_5863.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___737_5863.FStar_TypeChecker_Cfg.reifying}) tm))

type norm_request_t =
| Norm_request_none
| Norm_request_ready
| Norm_request_requires_rejig


let uu___is_Norm_request_none : norm_request_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Norm_request_none -> begin
true
end
| uu____5877 -> begin
false
end))


let uu___is_Norm_request_ready : norm_request_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Norm_request_ready -> begin
true
end
| uu____5888 -> begin
false
end))


let uu___is_Norm_request_requires_rejig : norm_request_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Norm_request_requires_rejig -> begin
true
end
| uu____5899 -> begin
false
end))


let is_norm_request : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  norm_request_t = (fun hd1 args -> (

let aux = (fun min_args -> (

let uu____5920 = (FStar_All.pipe_right args FStar_List.length)
in (FStar_All.pipe_right uu____5920 (fun n1 -> (match ((n1 < min_args)) with
| true -> begin
Norm_request_none
end
| uu____5946 -> begin
(match ((Prims.op_Equality n1 min_args)) with
| true -> begin
Norm_request_ready
end
| uu____5950 -> begin
Norm_request_requires_rejig
end)
end)))))
in (

let uu____5952 = (

let uu____5953 = (FStar_Syntax_Util.un_uinst hd1)
in uu____5953.FStar_Syntax_Syntax.n)
in (match (uu____5952) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term) -> begin
(aux (Prims.parse_int "2"))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize) -> begin
(aux (Prims.parse_int "1"))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm) -> begin
(aux (Prims.parse_int "3"))
end
| uu____5962 -> begin
Norm_request_none
end))))


let should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg  ->  Prims.bool = (fun cfg -> ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.no_full_norm)) && (

let uu____5971 = (FStar_Ident.lid_equals cfg.FStar_TypeChecker_Cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid)
in (not (uu____5971)))))


let rejig_norm_request : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term = (fun hd1 args -> (

let uu____5984 = (

let uu____5985 = (FStar_Syntax_Util.un_uinst hd1)
in uu____5985.FStar_Syntax_Syntax.n)
in (match (uu____5984) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term) -> begin
(match (args) with
| (t1)::(t2)::rest when ((FStar_List.length rest) > (Prims.parse_int "0")) -> begin
(

let uu____6043 = (FStar_Syntax_Util.mk_app hd1 ((t1)::(t2)::[]))
in (FStar_Syntax_Util.mk_app uu____6043 rest))
end
| uu____6070 -> begin
(failwith "Impossible! invalid rejig_norm_request for normalize_term")
end)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize) -> begin
(match (args) with
| (t)::rest when ((FStar_List.length rest) > (Prims.parse_int "0")) -> begin
(

let uu____6110 = (FStar_Syntax_Util.mk_app hd1 ((t)::[]))
in (FStar_Syntax_Util.mk_app uu____6110 rest))
end
| uu____6129 -> begin
(failwith "Impossible! invalid rejig_norm_request for normalize")
end)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm) -> begin
(match (args) with
| (t1)::(t2)::(t3)::rest when ((FStar_List.length rest) > (Prims.parse_int "0")) -> begin
(

let uu____6203 = (FStar_Syntax_Util.mk_app hd1 ((t1)::(t2)::(t3)::[]))
in (FStar_Syntax_Util.mk_app uu____6203 rest))
end
| uu____6238 -> begin
(failwith "Impossible! invalid rejig_norm_request for norm")
end)
end
| uu____6240 -> begin
(

let uu____6241 = (

let uu____6243 = (FStar_Syntax_Print.term_to_string hd1)
in (FStar_String.op_Hat "Impossible! invalid rejig_norm_request for: %s" uu____6243))
in (failwith uu____6241))
end)))


let is_nbe_request : FStar_TypeChecker_Env.step Prims.list  ->  Prims.bool = (fun s -> (FStar_Util.for_some (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s))


let tr_norm_step : FStar_Syntax_Embeddings.norm_step  ->  FStar_TypeChecker_Env.step Prims.list = (fun uu___9_6264 -> (match (uu___9_6264) with
| FStar_Syntax_Embeddings.Zeta -> begin
(FStar_TypeChecker_Env.Zeta)::[]
end
| FStar_Syntax_Embeddings.Iota -> begin
(FStar_TypeChecker_Env.Iota)::[]
end
| FStar_Syntax_Embeddings.Delta -> begin
(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]
end
| FStar_Syntax_Embeddings.Simpl -> begin
(FStar_TypeChecker_Env.Simplify)::[]
end
| FStar_Syntax_Embeddings.Weak -> begin
(FStar_TypeChecker_Env.Weak)::[]
end
| FStar_Syntax_Embeddings.HNF -> begin
(FStar_TypeChecker_Env.HNF)::[]
end
| FStar_Syntax_Embeddings.Primops -> begin
(FStar_TypeChecker_Env.Primops)::[]
end
| FStar_Syntax_Embeddings.Reify -> begin
(FStar_TypeChecker_Env.Reify)::[]
end
| FStar_Syntax_Embeddings.UnfoldOnly (names1) -> begin
(

let uu____6271 = (

let uu____6274 = (

let uu____6275 = (FStar_List.map FStar_Ident.lid_of_str names1)
in FStar_TypeChecker_Env.UnfoldOnly (uu____6275))
in (uu____6274)::[])
in (FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::uu____6271)
end
| FStar_Syntax_Embeddings.UnfoldFully (names1) -> begin
(

let uu____6283 = (

let uu____6286 = (

let uu____6287 = (FStar_List.map FStar_Ident.lid_of_str names1)
in FStar_TypeChecker_Env.UnfoldFully (uu____6287))
in (uu____6286)::[])
in (FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::uu____6283)
end
| FStar_Syntax_Embeddings.UnfoldAttr (names1) -> begin
(

let uu____6295 = (

let uu____6298 = (

let uu____6299 = (FStar_List.map FStar_Ident.lid_of_str names1)
in FStar_TypeChecker_Env.UnfoldAttr (uu____6299))
in (uu____6298)::[])
in (FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::uu____6295)
end
| FStar_Syntax_Embeddings.NBE -> begin
(FStar_TypeChecker_Env.NBE)::[]
end))


let tr_norm_steps : FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_TypeChecker_Env.step Prims.list = (fun s -> (

let s1 = (FStar_List.concatMap tr_norm_step s)
in (

let add_exclude = (fun s2 z -> (

let uu____6335 = (FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s2)
in (match (uu____6335) with
| true -> begin
s2
end
| uu____6340 -> begin
(FStar_TypeChecker_Env.Exclude (z))::s2
end)))
in (

let s2 = (FStar_TypeChecker_Env.Beta)::s1
in (

let s3 = (add_exclude s2 FStar_TypeChecker_Env.Zeta)
in (

let s4 = (add_exclude s3 FStar_TypeChecker_Env.Iota)
in s4))))))


let get_norm_request : 'Auu____6360 . FStar_TypeChecker_Cfg.cfg  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term * 'Auu____6360) Prims.list  ->  (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun cfg full_norm args -> (

let parse_steps = (fun s -> (

let uu____6411 = (

let uu____6416 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_norm_step)
in (FStar_TypeChecker_Cfg.try_unembed_simple uu____6416 s))
in (match (uu____6411) with
| FStar_Pervasives_Native.Some (steps) -> begin
(

let uu____6432 = (tr_norm_steps steps)
in FStar_Pervasives_Native.Some (uu____6432))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))
in (

let inherited_steps = (FStar_List.append (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.erase_universes) with
| true -> begin
(FStar_TypeChecker_Env.EraseUniverses)::[]
end
| uu____6447 -> begin
[]
end) (FStar_List.append (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.allow_unbound_universes) with
| true -> begin
(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]
end
| uu____6452 -> begin
[]
end) (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.nbe_step) with
| true -> begin
(FStar_TypeChecker_Env.NBE)::[]
end
| uu____6457 -> begin
[]
end)))
in (match (args) with
| (uu____6467)::((tm, uu____6469))::[] -> begin
(

let s = (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Reify)::[]
in FStar_Pervasives_Native.Some ((((FStar_List.append inherited_steps s)), (tm))))
end
| ((tm, uu____6498))::[] -> begin
(

let s = (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Reify)::[]
in FStar_Pervasives_Native.Some ((((FStar_List.append inherited_steps s)), (tm))))
end
| ((steps, uu____6519))::(uu____6520)::((tm, uu____6522))::[] -> begin
(

let uu____6543 = (

let uu____6548 = (full_norm steps)
in (parse_steps uu____6548))
in (match (uu____6543) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s) -> begin
FStar_Pervasives_Native.Some ((((FStar_List.append inherited_steps s)), (tm)))
end))
end
| uu____6578 -> begin
FStar_Pervasives_Native.None
end))))


let nbe_eval : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_Env.steps  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg s tm -> (

let delta_level = (

let uu____6610 = (FStar_All.pipe_right s (FStar_Util.for_some (fun uu___10_6617 -> (match (uu___10_6617) with
| FStar_TypeChecker_Env.UnfoldUntil (uu____6619) -> begin
true
end
| FStar_TypeChecker_Env.UnfoldOnly (uu____6621) -> begin
true
end
| FStar_TypeChecker_Env.UnfoldFully (uu____6625) -> begin
true
end
| uu____6629 -> begin
false
end))))
in (match (uu____6610) with
| true -> begin
(FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]
end
| uu____6634 -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end))
in ((FStar_TypeChecker_Cfg.log_nbe cfg (fun uu____6639 -> (

let uu____6640 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Invoking NBE with  %s\n" uu____6640))));
(

let tm_norm = (

let uu____6644 = (

let uu____6659 = (FStar_TypeChecker_Cfg.cfg_env cfg)
in uu____6659.FStar_TypeChecker_Env.nbe)
in (uu____6644 s cfg.FStar_TypeChecker_Cfg.tcenv tm))
in ((FStar_TypeChecker_Cfg.log_nbe cfg (fun uu____6663 -> (

let uu____6664 = (FStar_Syntax_Print.term_to_string tm_norm)
in (FStar_Util.print1 "Result of NBE is  %s\n" uu____6664))));
tm_norm;
));
)))


let firstn : 'Auu____6674 . Prims.int  ->  'Auu____6674 Prims.list  ->  ('Auu____6674 Prims.list * 'Auu____6674 Prims.list) = (fun k l -> (match (((FStar_List.length l) < k)) with
| true -> begin
((l), ([]))
end
| uu____6704 -> begin
(FStar_Util.first_N k l)
end))


let should_reify : FStar_TypeChecker_Cfg.cfg  ->  stack_elt Prims.list  ->  Prims.bool = (fun cfg stack -> (

let rec drop_irrel = (fun uu___11_6731 -> (match (uu___11_6731) with
| (MemoLazy (uu____6736))::s -> begin
(drop_irrel s)
end
| (UnivArgs (uu____6746))::s -> begin
(drop_irrel s)
end
| s -> begin
s
end))
in (

let uu____6759 = (drop_irrel stack)
in (match (uu____6759) with
| (App (uu____6763, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____6764; FStar_Syntax_Syntax.vars = uu____6765}, uu____6766, uu____6767))::uu____6768 -> begin
cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.reify_
end
| uu____6773 -> begin
false
end))))


let rec maybe_weakly_reduced : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun tm -> (

let aux_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (t, uu____6802) -> begin
(maybe_weakly_reduced t)
end
| FStar_Syntax_Syntax.Total (t, uu____6812) -> begin
(maybe_weakly_reduced t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
((maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) || (FStar_Util.for_some (fun uu____6833 -> (match (uu____6833) with
| (a, uu____6844) -> begin
(maybe_weakly_reduced a)
end)) ct.FStar_Syntax_Syntax.effect_args))
end))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____6855) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (uu____6880) -> begin
false
end
| FStar_Syntax_Syntax.Tm_uvar (uu____6882) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____6896) -> begin
false
end
| FStar_Syntax_Syntax.Tm_bvar (uu____6898) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (uu____6900) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____6902) -> begin
false
end
| FStar_Syntax_Syntax.Tm_lazy (uu____6904) -> begin
false
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| FStar_Syntax_Syntax.Tm_uinst (uu____6907) -> begin
false
end
| FStar_Syntax_Syntax.Tm_quoted (uu____6915) -> begin
false
end
| FStar_Syntax_Syntax.Tm_let (uu____6923) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____6938) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____6958) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____6974) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____6982) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
((maybe_weakly_reduced t1) || (FStar_All.pipe_right args (FStar_Util.for_some (fun uu____7054 -> (match (uu____7054) with
| (a, uu____7065) -> begin
(maybe_weakly_reduced a)
end)))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____7076) -> begin
(((maybe_weakly_reduced t1) || (match ((FStar_Pervasives_Native.fst asc)) with
| FStar_Util.Inl (t2) -> begin
(maybe_weakly_reduced t2)
end
| FStar_Util.Inr (c2) -> begin
(aux_comp c2)
end)) || (match ((FStar_Pervasives_Native.snd asc)) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (tac) -> begin
(maybe_weakly_reduced tac)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
((maybe_weakly_reduced t1) || (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (uu____7175, args) -> begin
(FStar_Util.for_some (FStar_Util.for_some (fun uu____7230 -> (match (uu____7230) with
| (a, uu____7241) -> begin
(maybe_weakly_reduced a)
end))) args)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____7250, uu____7251, t') -> begin
(maybe_weakly_reduced t')
end
| FStar_Syntax_Syntax.Meta_monadic (uu____7257, t') -> begin
(maybe_weakly_reduced t')
end
| FStar_Syntax_Syntax.Meta_labeled (uu____7263) -> begin
false
end
| FStar_Syntax_Syntax.Meta_desugared (uu____7273) -> begin
false
end
| FStar_Syntax_Syntax.Meta_named (uu____7275) -> begin
false
end))
end))))

type should_unfold_res =
| Should_unfold_no
| Should_unfold_yes
| Should_unfold_fully
| Should_unfold_reify


let uu___is_Should_unfold_no : should_unfold_res  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Should_unfold_no -> begin
true
end
| uu____7286 -> begin
false
end))


let uu___is_Should_unfold_yes : should_unfold_res  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Should_unfold_yes -> begin
true
end
| uu____7297 -> begin
false
end))


let uu___is_Should_unfold_fully : should_unfold_res  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Should_unfold_fully -> begin
true
end
| uu____7308 -> begin
false
end))


let uu___is_Should_unfold_reify : should_unfold_res  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Should_unfold_reify -> begin
true
end
| uu____7319 -> begin
false
end))


let should_unfold : FStar_TypeChecker_Cfg.cfg  ->  (FStar_TypeChecker_Cfg.cfg  ->  Prims.bool)  ->  FStar_Syntax_Syntax.fv  ->  FStar_TypeChecker_Env.qninfo  ->  should_unfold_res = (fun cfg should_reify1 fv qninfo -> (

let attrs = (

let uu____7352 = (FStar_TypeChecker_Env.attrs_of_qninfo qninfo)
in (match (uu____7352) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (ats) -> begin
ats
end))
in (

let yes = ((true), (false), (false))
in (

let no = ((false), (false), (false))
in (

let fully = ((true), (true), (false))
in (

let reif = ((true), (false), (true))
in (

let yesno = (fun b -> (match (b) with
| true -> begin
yes
end
| uu____7457 -> begin
no
end))
in (

let fullyno = (fun b -> (match (b) with
| true -> begin
fully
end
| uu____7486 -> begin
no
end))
in (

let comb_or = (fun l -> (FStar_List.fold_right (fun uu____7551 uu____7552 -> (match (((uu____7551), (uu____7552))) with
| ((a, b, c), (x, y, z)) -> begin
(((a || x)), ((b || y)), ((c || z)))
end)) l ((false), (false), (false))))
in (

let string_of_res = (fun uu____7658 -> (match (uu____7658) with
| (x, y, z) -> begin
(

let uu____7678 = (FStar_Util.string_of_bool x)
in (

let uu____7680 = (FStar_Util.string_of_bool y)
in (

let uu____7682 = (FStar_Util.string_of_bool z)
in (FStar_Util.format3 "(%s,%s,%s)" uu____7678 uu____7680 uu____7682))))
end))
in (

let res = if (FStar_TypeChecker_Env.qninfo_is_action qninfo) then begin
(

let b = (should_reify1 cfg)
in ((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7710 -> (

let uu____7711 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____7713 = (FStar_Util.string_of_bool b)
in (FStar_Util.print2 "should_unfold: For DM4F action %s, should_reify = %s\n" uu____7711 uu____7713)))));
(match (b) with
| true -> begin
reif
end
| uu____7726 -> begin
no
end);
))
end else begin
if (

let uu____7728 = (FStar_TypeChecker_Cfg.find_prim_step cfg fv)
in (FStar_Option.isSome uu____7728)) then begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7733 -> (FStar_Util.print_string " >> It\'s a primop, not unfolding\n")));
no;
)
end else begin
(match (((qninfo), (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_only), (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_fully), (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_attr))) with
| (FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, uu____7768), uu____7769); FStar_Syntax_Syntax.sigrng = uu____7770; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____7772; FStar_Syntax_Syntax.sigattrs = uu____7773; FStar_Syntax_Syntax.sigopts = uu____7774}, uu____7775), uu____7776), uu____7777, uu____7778, uu____7779) when (FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect qs) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7888 -> (FStar_Util.print_string " >> HasMaskedEffect, not unfolding\n")));
no;
)
end
| (uu____7890, uu____7891, uu____7892, uu____7893) when (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_tac && (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.tac_opaque_attr) attrs)) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7960 -> (FStar_Util.print_string " >> tac_opaque, not unfolding\n")));
no;
)
end
| (FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, uu____7963), uu____7964); FStar_Syntax_Syntax.sigrng = uu____7965; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____7967; FStar_Syntax_Syntax.sigattrs = uu____7968; FStar_Syntax_Syntax.sigopts = uu____7969}, uu____7970), uu____7971), uu____7972, uu____7973, uu____7974) when (is_rec && (not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta))) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8083 -> (FStar_Util.print_string " >> It\'s a recursive definition but we\'re not doing Zeta, not unfolding\n")));
no;
)
end
| (uu____8085, FStar_Pervasives_Native.Some (uu____8086), uu____8087, uu____8088) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8156 -> (

let uu____8157 = (FStar_Syntax_Print.fv_to_string fv)
in (FStar_Util.print1 "should_unfold: Reached a %s with selective unfolding\n" uu____8157))));
(

let uu____8160 = (

let uu____8172 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_only) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8198 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left yesno uu____8198))
end)
in (

let uu____8210 = (

let uu____8222 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_attr) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8248 = (FStar_Util.for_some (fun at -> (FStar_Util.for_some (fun lid -> (FStar_Syntax_Util.is_fvar lid at)) lids)) attrs)
in (FStar_All.pipe_left yesno uu____8248))
end)
in (

let uu____8264 = (

let uu____8276 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_fully) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8302 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left fullyno uu____8302))
end)
in (uu____8276)::[])
in (uu____8222)::uu____8264))
in (uu____8172)::uu____8210))
in (comb_or uu____8160));
)
end
| (uu____8350, uu____8351, FStar_Pervasives_Native.Some (uu____8352), uu____8353) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8421 -> (

let uu____8422 = (FStar_Syntax_Print.fv_to_string fv)
in (FStar_Util.print1 "should_unfold: Reached a %s with selective unfolding\n" uu____8422))));
(

let uu____8425 = (

let uu____8437 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_only) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8463 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left yesno uu____8463))
end)
in (

let uu____8475 = (

let uu____8487 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_attr) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8513 = (FStar_Util.for_some (fun at -> (FStar_Util.for_some (fun lid -> (FStar_Syntax_Util.is_fvar lid at)) lids)) attrs)
in (FStar_All.pipe_left yesno uu____8513))
end)
in (

let uu____8529 = (

let uu____8541 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_fully) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8567 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left fullyno uu____8567))
end)
in (uu____8541)::[])
in (uu____8487)::uu____8529))
in (uu____8437)::uu____8475))
in (comb_or uu____8425));
)
end
| (uu____8615, uu____8616, uu____8617, FStar_Pervasives_Native.Some (uu____8618)) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8686 -> (

let uu____8687 = (FStar_Syntax_Print.fv_to_string fv)
in (FStar_Util.print1 "should_unfold: Reached a %s with selective unfolding\n" uu____8687))));
(

let uu____8690 = (

let uu____8702 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_only) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8728 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left yesno uu____8728))
end)
in (

let uu____8740 = (

let uu____8752 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_attr) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8778 = (FStar_Util.for_some (fun at -> (FStar_Util.for_some (fun lid -> (FStar_Syntax_Util.is_fvar lid at)) lids)) attrs)
in (FStar_All.pipe_left yesno uu____8778))
end)
in (

let uu____8794 = (

let uu____8806 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_fully) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8832 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left fullyno uu____8832))
end)
in (uu____8806)::[])
in (uu____8752)::uu____8794))
in (uu____8702)::uu____8740))
in (comb_or uu____8690));
)
end
| uu____8880 -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8926 -> (

let uu____8927 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____8929 = (FStar_Syntax_Print.delta_depth_to_string fv.FStar_Syntax_Syntax.fv_delta)
in (

let uu____8931 = (FStar_Common.string_of_list FStar_TypeChecker_Env.string_of_delta_level cfg.FStar_TypeChecker_Cfg.delta_level)
in (FStar_Util.print3 "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n" uu____8927 uu____8929 uu____8931))))));
(

let uu____8934 = (FStar_All.pipe_right cfg.FStar_TypeChecker_Cfg.delta_level (FStar_Util.for_some (fun uu___12_8940 -> (match (uu___12_8940) with
| FStar_TypeChecker_Env.NoDelta -> begin
false
end
| FStar_TypeChecker_Env.InliningDelta -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| FStar_TypeChecker_Env.Unfold (l) -> begin
(

let uu____8946 = (FStar_TypeChecker_Env.delta_depth_of_fv cfg.FStar_TypeChecker_Cfg.tcenv fv)
in (FStar_TypeChecker_Common.delta_depth_greater_than uu____8946 l))
end))))
in (FStar_All.pipe_left yesno uu____8934));
)
end)
end
end
in ((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8962 -> (

let uu____8963 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____8965 = (

let uu____8967 = (FStar_Syntax_Syntax.range_of_fv fv)
in (FStar_Range.string_of_range uu____8967))
in (

let uu____8968 = (string_of_res res)
in (FStar_Util.print3 "should_unfold: For %s (%s), unfolding res = %s\n" uu____8963 uu____8965 uu____8968))))));
(match (res) with
| (false, uu____8971, uu____8972) -> begin
Should_unfold_no
end
| (true, false, false) -> begin
Should_unfold_yes
end
| (true, true, false) -> begin
Should_unfold_fully
end
| (true, false, true) -> begin
Should_unfold_reify
end
| uu____8997 -> begin
(

let uu____9007 = (

let uu____9009 = (string_of_res res)
in (FStar_Util.format1 "Unexpected unfolding result: %s" uu____9009))
in (FStar_All.pipe_left failwith uu____9007))
end);
))))))))))))


let decide_unfolding : 'Auu____9028 . FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack_elt Prims.list  ->  'Auu____9028  ->  FStar_Syntax_Syntax.fv  ->  FStar_TypeChecker_Env.qninfo  ->  (FStar_TypeChecker_Cfg.cfg * stack_elt Prims.list) FStar_Pervasives_Native.option = (fun cfg env stack rng fv qninfo -> (

let res = (should_unfold cfg (fun cfg1 -> (should_reify cfg1 stack)) fv qninfo)
in (match (res) with
| Should_unfold_no -> begin
FStar_Pervasives_Native.None
end
| Should_unfold_yes -> begin
FStar_Pervasives_Native.Some (((cfg), (stack)))
end
| Should_unfold_fully -> begin
(

let cfg' = (

let uu___1147_9097 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___1149_9100 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___1149_9100.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___1149_9100.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___1149_9100.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___1149_9100.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___1149_9100.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___1149_9100.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___1149_9100.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant); FStar_TypeChecker_Cfg.unfold_only = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_fully = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_attr = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_tac = uu___1149_9100.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___1149_9100.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___1149_9100.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___1149_9100.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___1149_9100.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___1149_9100.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___1149_9100.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___1149_9100.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___1149_9100.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___1149_9100.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___1149_9100.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___1149_9100.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___1149_9100.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___1149_9100.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___1149_9100.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___1147_9097.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1147_9097.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1147_9097.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1147_9097.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1147_9097.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1147_9097.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1147_9097.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1147_9097.FStar_TypeChecker_Cfg.reifying})
in (

let stack' = (match (stack) with
| (UnivArgs (us, r))::stack' -> begin
(UnivArgs (((us), (r))))::(Cfg (cfg))::stack'
end
| stack' -> begin
(Cfg (cfg))::stack'
end)
in FStar_Pervasives_Native.Some (((cfg'), (stack')))))
end
| Should_unfold_reify -> begin
(

let rec push1 = (fun e s -> (match (s) with
| [] -> begin
(e)::[]
end
| (UnivArgs (us, r))::t -> begin
(

let uu____9162 = (push1 e t)
in (UnivArgs (((us), (r))))::uu____9162)
end
| (h)::t -> begin
(e)::(h)::t
end))
in (

let ref = (

let uu____9174 = (

let uu____9181 = (

let uu____9182 = (

let uu____9183 = (FStar_Syntax_Syntax.lid_of_fv fv)
in FStar_Const.Const_reflect (uu____9183))
in FStar_Syntax_Syntax.Tm_constant (uu____9182))
in (FStar_Syntax_Syntax.mk uu____9181))
in (uu____9174 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let stack1 = (push1 (App (((env), (ref), (FStar_Pervasives_Native.None), (FStar_Range.dummyRange)))) stack)
in FStar_Pervasives_Native.Some (((cfg), (stack1))))))
end)))


let on_domain_lids : FStar_Ident.lident Prims.list = (

let fext_lid = (fun s -> (FStar_Ident.lid_of_path (("FStar")::("FunctionalExtensionality")::(s)::[]) FStar_Range.dummyRange))
in (FStar_All.pipe_right (("on_domain")::("on_dom")::("on_domain_g")::("on_dom_g")::[]) (FStar_List.map fext_lid)))


let is_fext_on_domain : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let is_on_dom = (fun fv -> (FStar_All.pipe_right on_domain_lids (FStar_List.existsb (fun l -> (FStar_Syntax_Syntax.fv_eq_lid fv l)))))
in (

let uu____9249 = (

let uu____9250 = (FStar_Syntax_Subst.compress t)
in uu____9250.FStar_Syntax_Syntax.n)
in (match (uu____9249) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____9281 = (

let uu____9282 = (FStar_Syntax_Util.un_uinst hd1)
in uu____9282.FStar_Syntax_Syntax.n)
in (match (uu____9281) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((is_on_dom fv) && (Prims.op_Equality (FStar_List.length args) (Prims.parse_int "3"))) -> begin
(

let f = (

let uu____9299 = (

let uu____9306 = (

let uu____9317 = (FStar_All.pipe_right args FStar_List.tl)
in (FStar_All.pipe_right uu____9317 FStar_List.tl))
in (FStar_All.pipe_right uu____9306 FStar_List.hd))
in (FStar_All.pipe_right uu____9299 FStar_Pervasives_Native.fst))
in FStar_Pervasives_Native.Some (f))
end
| uu____9416 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____9417 -> begin
FStar_Pervasives_Native.None
end))))


let rec norm : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t1 = ((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.norm_delayed) with
| true -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____9696) -> begin
(

let uu____9719 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "NORM delayed: %s\n" uu____9719))
end
| uu____9722 -> begin
()
end)
end
| uu____9723 -> begin
()
end);
(FStar_Syntax_Subst.compress t);
)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____9732 -> (

let uu____9733 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____9735 = (FStar_Util.string_of_bool cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.no_full_norm)
in (

let uu____9737 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____9739 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____9747 = (

let uu____9749 = (

let uu____9752 = (firstn (Prims.parse_int "4") stack)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9752))
in (stack_to_string uu____9749))
in (FStar_Util.print5 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n" uu____9733 uu____9735 uu____9737 uu____9739 uu____9747))))))));
(FStar_TypeChecker_Cfg.log_cfg cfg (fun uu____9780 -> (

let uu____9781 = (FStar_TypeChecker_Cfg.cfg_to_string cfg)
in (FStar_Util.print1 ">>> cfg = %s\n" uu____9781))));
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9787 -> (

let uu____9788 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9788))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_constant (uu____9791) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9795 -> (

let uu____9796 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9796))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_name (uu____9799) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9803 -> (

let uu____9804 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9804))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_lazy (uu____9807) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9811 -> (

let uu____9812 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9812))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____9815; FStar_Syntax_Syntax.fv_delta = uu____9816; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9820 -> (

let uu____9821 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9821))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____9824; FStar_Syntax_Syntax.fv_delta = uu____9825; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____9826))}) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9836 -> (

let uu____9837 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9837))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let qninfo = (FStar_TypeChecker_Env.lookup_qname cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (

let uu____9843 = (FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo)
in (match (uu____9843) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level (_9846)) when (_9846 = (Prims.parse_int "0")) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9850 -> (

let uu____9851 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9851))));
(rebuild cfg env stack t1);
)
end
| uu____9854 -> begin
(

let uu____9857 = (decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv qninfo)
in (match (uu____9857) with
| FStar_Pervasives_Native.Some (cfg1, stack1) -> begin
(do_unfold_fv cfg1 env stack1 t1 qninfo fv)
end
| FStar_Pervasives_Native.None -> begin
(rebuild cfg env stack t1)
end))
end))))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, qi) -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted (norm cfg env []) qi)
in (

let t2 = (mk (FStar_Syntax_Syntax.Tm_quoted (((qt), (qi1)))) t1.FStar_Syntax_Syntax.pos)
in (

let uu____9896 = (closure_as_term cfg env t2)
in (rebuild cfg env stack uu____9896))))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when ((should_consider_norm_requests cfg) && (

let uu____9924 = (is_norm_request hd1 args)
in (Prims.op_Equality uu____9924 Norm_request_requires_rejig))) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(FStar_Util.print_string "Rejigging norm request ... \n")
end
| uu____9928 -> begin
()
end);
(

let uu____9930 = (rejig_norm_request hd1 args)
in (norm cfg env stack uu____9930));
)
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when ((should_consider_norm_requests cfg) && (

let uu____9958 = (is_norm_request hd1 args)
in (Prims.op_Equality uu____9958 Norm_request_ready))) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(FStar_Util.print_string "Potential norm request ... \n")
end
| uu____9962 -> begin
()
end);
(

let cfg' = (

let uu___1260_9965 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___1262_9968 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___1262_9968.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___1262_9968.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___1262_9968.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___1262_9968.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___1262_9968.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___1262_9968.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = false; FStar_TypeChecker_Cfg.unfold_until = uu___1262_9968.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_fully = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_attr = uu___1262_9968.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___1262_9968.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___1262_9968.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___1262_9968.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___1262_9968.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___1262_9968.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___1262_9968.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___1262_9968.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___1262_9968.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___1262_9968.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___1262_9968.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___1262_9968.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___1262_9968.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___1262_9968.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___1262_9968.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___1262_9968.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___1260_9965.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1260_9965.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]; FStar_TypeChecker_Cfg.primitive_steps = uu___1260_9965.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1260_9965.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1260_9965.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = true; FStar_TypeChecker_Cfg.reifying = uu___1260_9965.FStar_TypeChecker_Cfg.reifying})
in (

let uu____9975 = (get_norm_request cfg (norm cfg' env []) args)
in (match (uu____9975) with
| FStar_Pervasives_Native.None -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(FStar_Util.print_string "Norm request None ... \n")
end
| uu____9995 -> begin
()
end);
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____10011 stack1 -> (match (uu____10011) with
| (a, aq) -> begin
(

let uu____10023 = (

let uu____10024 = (

let uu____10031 = (

let uu____10032 = (

let uu____10064 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____10064), (false)))
in Clos (uu____10032))
in ((uu____10031), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____10024))
in (uu____10023)::stack1)
end)) args))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10132 -> (

let uu____10133 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____10133))));
(norm cfg env stack1 hd1);
));
)
end
| FStar_Pervasives_Native.Some (s, tm) when (is_nbe_request s) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(

let uu____10160 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Starting NBE request on %s ... \n" uu____10160))
end
| uu____10163 -> begin
()
end);
(

let tm' = (closure_as_term cfg env tm)
in (

let start = (FStar_Util.now ())
in (

let tm_norm = (nbe_eval cfg s tm')
in (

let fin = (FStar_Util.now ())
in ((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(

let uu____10171 = (

let uu____10173 = (

let uu____10175 = (FStar_Util.time_diff start fin)
in (FStar_Pervasives_Native.snd uu____10175))
in (FStar_Util.string_of_int uu____10173))
in (

let uu____10182 = (FStar_Syntax_Print.term_to_string tm')
in (

let uu____10184 = (FStar_Syntax_Print.term_to_string tm_norm)
in (FStar_Util.print3 "NBE\'d (%s ms) %s\n\tto %s\n" uu____10171 uu____10182 uu____10184))))
end
| uu____10187 -> begin
()
end);
(norm cfg env stack tm_norm);
)))));
)
end
| FStar_Pervasives_Native.Some (s, tm) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(

let uu____10203 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Starting norm request on %s ... \n" uu____10203))
end
| uu____10206 -> begin
()
end);
(

let delta_level = (

let uu____10211 = (FStar_All.pipe_right s (FStar_Util.for_some (fun uu___13_10218 -> (match (uu___13_10218) with
| FStar_TypeChecker_Env.UnfoldUntil (uu____10220) -> begin
true
end
| FStar_TypeChecker_Env.UnfoldOnly (uu____10222) -> begin
true
end
| FStar_TypeChecker_Env.UnfoldFully (uu____10226) -> begin
true
end
| uu____10230 -> begin
false
end))))
in (match (uu____10211) with
| true -> begin
(FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]
end
| uu____10235 -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end))
in (

let cfg'1 = (

let uu___1303_10238 = cfg
in (

let uu____10239 = (

let uu___1305_10240 = (FStar_TypeChecker_Cfg.to_fsteps s)
in {FStar_TypeChecker_Cfg.beta = uu___1305_10240.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___1305_10240.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___1305_10240.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___1305_10240.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___1305_10240.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___1305_10240.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___1305_10240.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___1305_10240.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___1305_10240.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___1305_10240.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___1305_10240.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___1305_10240.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___1305_10240.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___1305_10240.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___1305_10240.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___1305_10240.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___1305_10240.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___1305_10240.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___1305_10240.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___1305_10240.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___1305_10240.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___1305_10240.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = true; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___1305_10240.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___1305_10240.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___1305_10240.FStar_TypeChecker_Cfg.for_extraction})
in {FStar_TypeChecker_Cfg.steps = uu____10239; FStar_TypeChecker_Cfg.tcenv = uu___1303_10238.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1303_10238.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1303_10238.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1303_10238.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1303_10238.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = true; FStar_TypeChecker_Cfg.reifying = uu___1303_10238.FStar_TypeChecker_Cfg.reifying}))
in (

let stack' = (

let tail1 = (Cfg (cfg))::stack
in (match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(

let uu____10248 = (

let uu____10249 = (

let uu____10254 = (FStar_Util.now ())
in ((t1), (uu____10254)))
in Debug (uu____10249))
in (uu____10248)::tail1)
end
| uu____10255 -> begin
tail1
end))
in (norm cfg'1 env stack' tm))));
)
end)));
)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u1 = (norm_universe cfg env u)
in (

let uu____10259 = (mk (FStar_Syntax_Syntax.Tm_type (u1)) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack uu____10259)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.erase_universes) with
| true -> begin
(norm cfg env stack t')
end
| uu____10267 -> begin
(

let us1 = (

let uu____10270 = (

let uu____10277 = (FStar_List.map (norm_universe cfg env) us)
in ((uu____10277), (t1.FStar_Syntax_Syntax.pos)))
in UnivArgs (uu____10270))
in (

let stack1 = (us1)::stack
in (norm cfg env stack1 t')))
end)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____10286 = (lookup_bvar env x)
in (match (uu____10286) with
| Univ (uu____10287) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env1, t0, r, fix) -> begin
(match (((not (fix)) || cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta)) with
| true -> begin
(

let uu____10341 = (FStar_ST.op_Bang r)
in (match (uu____10341) with
| FStar_Pervasives_Native.Some (env2, t') -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____10437 -> (

let uu____10438 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10440 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" uu____10438 uu____10440)))));
(

let uu____10443 = (maybe_weakly_reduced t')
in (match (uu____10443) with
| true -> begin
(match (stack) with
| [] when (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak || cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars) -> begin
(rebuild cfg env2 stack t')
end
| uu____10446 -> begin
(norm cfg env2 stack t')
end)
end
| uu____10447 -> begin
(rebuild cfg env2 stack t')
end));
)
end
| FStar_Pervasives_Native.None -> begin
(norm cfg env1 ((MemoLazy (r))::stack) t0)
end))
end
| uu____10461 -> begin
(norm cfg env1 stack t0)
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack) with
| (UnivArgs (uu____10490))::uu____10491 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Arg (c, uu____10502, uu____10503))::stack_rest -> begin
(match (c) with
| Univ (uu____10507) -> begin
(norm cfg ((((FStar_Pervasives_Native.None), (c)))::env) stack_rest t1)
end
| uu____10516 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (b)::[] -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____10546 -> (

let uu____10547 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____10547))));
(norm cfg ((((FStar_Pervasives_Native.Some (b)), (c)))::env) stack_rest body);
)
end
| (b)::tl1 -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____10583 -> (

let uu____10584 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____10584))));
(

let body1 = (mk (FStar_Syntax_Syntax.Tm_abs (((tl1), (body), (lopt)))) t1.FStar_Syntax_Syntax.pos)
in (norm cfg ((((FStar_Pervasives_Native.Some (b)), (c)))::env) stack_rest body1));
)
end)
end)
end
| (Cfg (cfg1))::stack1 -> begin
(norm cfg1 env stack1 t1)
end
| (MemoLazy (r))::stack1 -> begin
((set_memo cfg r ((env), (t1)));
(FStar_TypeChecker_Cfg.log cfg (fun uu____10632 -> (

let uu____10633 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____10633))));
(norm cfg env stack1 t1);
)
end
| (Match (uu____10636))::uu____10637 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____10650 -> begin
(

let uu____10652 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____10652) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____10688 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____10732 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____10732))))
end
| uu____10733 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1423_10740 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1423_10740.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1423_10740.FStar_Syntax_Syntax.residual_flags})))
end
| uu____10741 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10747 -> (

let uu____10748 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____10748))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1430_10763 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1430_10763.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1430_10763.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1430_10763.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1430_10763.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1430_10763.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1430_10763.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1430_10763.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1430_10763.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Debug (uu____10767))::uu____10768 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____10777 -> begin
(

let uu____10779 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____10779) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____10815 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____10859 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____10859))))
end
| uu____10860 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1423_10867 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1423_10867.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1423_10867.FStar_Syntax_Syntax.residual_flags})))
end
| uu____10868 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10874 -> (

let uu____10875 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____10875))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1430_10890 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1430_10890.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1430_10890.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1430_10890.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1430_10890.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1430_10890.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1430_10890.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1430_10890.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1430_10890.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Meta (uu____10894))::uu____10895 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____10906 -> begin
(

let uu____10908 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____10908) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____10944 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____10988 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____10988))))
end
| uu____10989 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1423_10996 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1423_10996.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1423_10996.FStar_Syntax_Syntax.residual_flags})))
end
| uu____10997 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11003 -> (

let uu____11004 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11004))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1430_11019 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1430_11019.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1430_11019.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1430_11019.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1430_11019.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1430_11019.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1430_11019.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1430_11019.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1430_11019.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Let (uu____11023))::uu____11024 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____11037 -> begin
(

let uu____11039 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11039) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11075 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11119 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11119))))
end
| uu____11120 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1423_11127 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1423_11127.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1423_11127.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11128 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11134 -> (

let uu____11135 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11135))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1430_11150 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1430_11150.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1430_11150.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1430_11150.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1430_11150.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1430_11150.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1430_11150.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1430_11150.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1430_11150.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (App (uu____11154))::uu____11155 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____11168 -> begin
(

let uu____11170 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11170) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11206 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11250 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11250))))
end
| uu____11251 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1423_11258 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1423_11258.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1423_11258.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11259 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11265 -> (

let uu____11266 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11266))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1430_11281 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1430_11281.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1430_11281.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1430_11281.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1430_11281.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1430_11281.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1430_11281.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1430_11281.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1430_11281.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Abs (uu____11285))::uu____11286 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____11303 -> begin
(

let uu____11305 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11305) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11341 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11385 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11385))))
end
| uu____11386 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1423_11393 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1423_11393.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1423_11393.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11394 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11400 -> (

let uu____11401 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11401))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1430_11416 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1430_11416.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1430_11416.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1430_11416.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1430_11416.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1430_11416.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1430_11416.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1430_11416.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1430_11416.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| [] -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____11422 -> begin
(

let uu____11424 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11424) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11460 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11504 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11504))))
end
| uu____11505 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1423_11512 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1423_11512.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1423_11512.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11513 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11519 -> (

let uu____11520 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11520))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1430_11535 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1430_11535.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1430_11535.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1430_11535.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1430_11535.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1430_11535.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1430_11535.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1430_11535.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1430_11535.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let strict_args = (

let uu____11571 = (

let uu____11572 = (FStar_Syntax_Util.un_uinst head1)
in uu____11572.FStar_Syntax_Syntax.n)
in (match (uu____11571) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_TypeChecker_Env.fv_has_strict_args cfg.FStar_TypeChecker_Cfg.tcenv fv)
end
| uu____11581 -> begin
FStar_Pervasives_Native.None
end))
in (match (strict_args) with
| FStar_Pervasives_Native.None -> begin
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____11602 stack1 -> (match (uu____11602) with
| (a, aq) -> begin
(

let uu____11614 = (

let uu____11615 = (

let uu____11622 = (

let uu____11623 = (

let uu____11655 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____11655), (false)))
in Clos (uu____11623))
in ((uu____11622), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____11615))
in (uu____11614)::stack1)
end)) args))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11723 -> (

let uu____11724 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____11724))));
(norm cfg env stack1 head1);
))
end
| FStar_Pervasives_Native.Some (strict_args1) -> begin
(

let norm_args = (FStar_All.pipe_right args (FStar_List.map (fun uu____11775 -> (match (uu____11775) with
| (a, i) -> begin
(

let uu____11786 = (norm cfg env [] a)
in ((uu____11786), (i)))
end))))
in (

let norm_args_len = (FStar_List.length norm_args)
in (

let uu____11792 = (FStar_All.pipe_right strict_args1 (FStar_List.for_all (fun i -> (match ((i >= norm_args_len)) with
| true -> begin
false
end
| uu____11805 -> begin
(

let uu____11807 = (FStar_List.nth norm_args i)
in (match (uu____11807) with
| (arg_i, uu____11818) -> begin
(

let uu____11819 = (FStar_Syntax_Util.head_and_args arg_i)
in (match (uu____11819) with
| (head2, uu____11838) -> begin
(

let uu____11863 = (

let uu____11864 = (FStar_Syntax_Util.un_uinst head2)
in uu____11864.FStar_Syntax_Syntax.n)
in (match (uu____11863) with
| FStar_Syntax_Syntax.Tm_constant (uu____11868) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____11871 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_TypeChecker_Env.is_datacon cfg.FStar_TypeChecker_Cfg.tcenv uu____11871))
end
| uu____11872 -> begin
false
end))
end))
end))
end))))
in (match (uu____11792) with
| true -> begin
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____11889 stack1 -> (match (uu____11889) with
| (a, aq) -> begin
(

let uu____11901 = (

let uu____11902 = (

let uu____11909 = (

let uu____11910 = (

let uu____11942 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ((([]), (a)))))
in ((env), (a), (uu____11942), (false)))
in Clos (uu____11910))
in ((uu____11909), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____11902))
in (uu____11901)::stack1)
end)) norm_args))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____12024 -> (

let uu____12025 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____12025))));
(norm cfg env stack1 head1);
))
end
| uu____12038 -> begin
(

let head2 = (closure_as_term cfg env head1)
in (

let term = (FStar_Syntax_Syntax.mk_Tm_app head2 norm_args FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack term)))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____12045) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.for_extraction -> begin
(norm cfg env stack x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(match (((env), (stack))) with
| ([], []) -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let t2 = (mk (FStar_Syntax_Syntax.Tm_refine ((((

let uu___1492_12090 = x
in {FStar_Syntax_Syntax.ppname = uu___1492_12090.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1492_12090.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t2)))
end
| uu____12091 -> begin
(

let uu____12106 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____12106))
end)
end
| uu____12107 -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let uu____12110 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____12110) with
| (closing, f1) -> begin
(

let f2 = (norm cfg ((dummy)::env) [] f1)
in (

let t2 = (

let uu____12141 = (

let uu____12142 = (

let uu____12149 = (FStar_Syntax_Subst.close closing f2)
in (((

let uu___1501_12155 = x
in {FStar_Syntax_Syntax.ppname = uu___1501_12155.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1501_12155.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (uu____12149)))
in FStar_Syntax_Syntax.Tm_refine (uu____12142))
in (mk uu____12141 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t2)))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let uu____12179 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____12179))
end
| uu____12180 -> begin
(

let uu____12182 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____12182) with
| (bs1, c1) -> begin
(

let c2 = (

let uu____12190 = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____12216 -> (dummy)::env1) env))
in (norm_comp cfg uu____12190 c1))
in (

let t2 = (

let uu____12240 = (norm_binders cfg env bs1)
in (FStar_Syntax_Util.arrow uu____12240 c2))
in (rebuild cfg env stack t2)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unascribe -> begin
(norm cfg env stack t11)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) -> begin
(match (stack) with
| (Match (uu____12353))::uu____12354 when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.beta -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12367 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (Arg (uu____12369))::uu____12370 when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.beta -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12381 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (App (uu____12383, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____12384; FStar_Syntax_Syntax.vars = uu____12385}, uu____12386, uu____12387))::uu____12388 when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.beta -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12395 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (MemoLazy (uu____12397))::uu____12398 when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.beta -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12409 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| uu____12411 -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12414 -> (FStar_Util.print_string "+++ Keeping ascription \n")));
(

let t12 = (norm cfg env [] t11)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____12419 -> (FStar_Util.print_string "+++ Normalizing ascription \n")));
(

let tc1 = (match (tc) with
| FStar_Util.Inl (t2) -> begin
(

let uu____12445 = (norm cfg env [] t2)
in FStar_Util.Inl (uu____12445))
end
| FStar_Util.Inr (c) -> begin
(

let uu____12459 = (norm_comp cfg env c)
in FStar_Util.Inr (uu____12459))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (norm cfg env []))
in (match (stack) with
| (Cfg (cfg1))::stack1 -> begin
(

let t2 = (

let uu____12482 = (

let uu____12483 = (

let uu____12510 = (FStar_Syntax_Util.unascribe t12)
in ((uu____12510), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____12483))
in (mk uu____12482 t1.FStar_Syntax_Syntax.pos))
in (norm cfg1 env stack1 t2))
end
| uu____12545 -> begin
(

let uu____12546 = (

let uu____12547 = (

let uu____12548 = (

let uu____12575 = (FStar_Syntax_Util.unascribe t12)
in ((uu____12575), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____12548))
in (mk uu____12547 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack uu____12546))
end)));
));
)
end)
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let stack1 = (Match (((env), (branches), (cfg), (t1.FStar_Syntax_Syntax.pos))))::stack
in (match (((cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.iota && cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee) && (not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak)))) with
| true -> begin
(

let cfg' = (

let uu___1580_12653 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___1582_12656 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___1582_12656.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___1582_12656.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___1582_12656.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = true; FStar_TypeChecker_Cfg.hnf = uu___1582_12656.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___1582_12656.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___1582_12656.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___1582_12656.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___1582_12656.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___1582_12656.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___1582_12656.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___1582_12656.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___1582_12656.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___1582_12656.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___1582_12656.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___1582_12656.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___1582_12656.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___1582_12656.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___1582_12656.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___1582_12656.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___1582_12656.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___1582_12656.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___1582_12656.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___1582_12656.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___1582_12656.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___1582_12656.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___1580_12653.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1580_12653.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1580_12653.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1580_12653.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1580_12653.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1580_12653.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1580_12653.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1580_12653.FStar_TypeChecker_Cfg.reifying})
in (norm cfg' env ((Cfg (cfg))::stack1) head1))
end
| uu____12658 -> begin
(norm cfg env stack1 head1)
end))
end
| FStar_Syntax_Syntax.Tm_let ((b, lbs), lbody) when ((FStar_Syntax_Syntax.is_top_level lbs) && cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____12697 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____12697) with
| (openings, lbunivs) -> begin
(

let cfg1 = (

let uu___1595_12717 = cfg
in (

let uu____12718 = (FStar_TypeChecker_Env.push_univ_vars cfg.FStar_TypeChecker_Cfg.tcenv lbunivs)
in {FStar_TypeChecker_Cfg.steps = uu___1595_12717.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu____12718; FStar_TypeChecker_Cfg.debug = uu___1595_12717.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1595_12717.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1595_12717.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1595_12717.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1595_12717.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1595_12717.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1595_12717.FStar_TypeChecker_Cfg.reifying}))
in (

let norm1 = (fun t2 -> (

let uu____12725 = (

let uu____12726 = (FStar_Syntax_Subst.subst openings t2)
in (norm cfg1 env [] uu____12726))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____12725)))
in (

let lbtyp = (norm1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (norm1 lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___1602_12729 = lb
in {FStar_Syntax_Syntax.lbname = uu___1602_12729.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___1602_12729.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___1602_12729.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1602_12729.FStar_Syntax_Syntax.lbpos})))))
end)))))
in (

let uu____12730 = (mk (FStar_Syntax_Syntax.Tm_let (((((b), (lbs1))), (lbody)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack uu____12730)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____12743, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____12744); FStar_Syntax_Syntax.lbunivs = uu____12745; FStar_Syntax_Syntax.lbtyp = uu____12746; FStar_Syntax_Syntax.lbeff = uu____12747; FStar_Syntax_Syntax.lbdef = uu____12748; FStar_Syntax_Syntax.lbattrs = uu____12749; FStar_Syntax_Syntax.lbpos = uu____12750})::uu____12751), uu____12752) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n1 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in (

let uu____12798 = ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets)) && (((cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.pure_subterms_within_computations && (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs FStar_Parser_Const.inline_let_attr)) || ((FStar_Syntax_Util.is_pure_effect n1) && (cfg.FStar_TypeChecker_Cfg.normalize_pure_lets || (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs FStar_Parser_Const.inline_let_attr)))) || ((FStar_Syntax_Util.is_ghost_effect n1) && (not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.pure_subterms_within_computations)))))
in (match (uu____12798) with
| true -> begin
(

let binder = (

let uu____12802 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____12802))
in (

let env1 = (

let uu____12812 = (

let uu____12819 = (

let uu____12820 = (

let uu____12852 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (uu____12852), (false)))
in Clos (uu____12820))
in ((FStar_Pervasives_Native.Some (binder)), (uu____12819)))
in (uu____12812)::env)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____12927 -> (FStar_Util.print_string "+++ Reducing Tm_let\n")));
(norm cfg env1 stack body);
)))
end
| uu____12929 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12934 -> (FStar_Util.print_string "+++ Not touching Tm_let\n")));
(

let uu____12936 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____12936));
)
end
| uu____12937 -> begin
(

let uu____12939 = (

let uu____12944 = (

let uu____12945 = (

let uu____12952 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right uu____12952 FStar_Syntax_Syntax.mk_binder))
in (uu____12945)::[])
in (FStar_Syntax_Subst.open_term uu____12944 body))
in (match (uu____12939) with
| (bs, body1) -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12979 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- type")));
(

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let x = (

let uu____12988 = (FStar_List.hd bs)
in (FStar_Pervasives_Native.fst uu____12988))
in FStar_Util.Inl ((

let uu___1644_13004 = x
in {FStar_Syntax_Syntax.ppname = uu___1644_13004.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1644_13004.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____13007 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- definiens\n")));
(

let lb1 = (

let uu___1649_13010 = lb
in (

let uu____13011 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___1649_13010.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___1649_13010.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____13011; FStar_Syntax_Syntax.lbattrs = uu___1649_13010.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1649_13010.FStar_Syntax_Syntax.lbpos}))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env1 uu____13040 -> (dummy)::env1) env))
in (

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1656_13065 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1656_13065.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1656_13065.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1656_13065.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1656_13065.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1656_13065.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1656_13065.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1656_13065.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1656_13065.FStar_TypeChecker_Cfg.reifying})
in ((FStar_TypeChecker_Cfg.log cfg1 (fun uu____13069 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- body\n")));
(norm cfg1 env' ((Let (((env), (bs), (lb1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1);
)))));
)));
)
end))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), body) when (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars || ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta)) && cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.pure_subterms_within_computations)) -> begin
(

let uu____13090 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____13090) with
| (lbs1, body1) -> begin
(

let lbs2 = (FStar_List.map (fun lb -> (

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let uu____13126 = (

let uu___1672_13127 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___1672_13127.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1672_13127.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})
in FStar_Util.Inl (uu____13126))
in (

let uu____13128 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____13128) with
| (xs, def_body, lopt) -> begin
(

let xs1 = (norm_binders cfg env xs)
in (

let env1 = (

let uu____13154 = (FStar_List.map (fun uu____13170 -> dummy) lbs1)
in (

let uu____13171 = (

let uu____13180 = (FStar_List.map (fun uu____13202 -> dummy) xs1)
in (FStar_List.append uu____13180 env))
in (FStar_List.append uu____13154 uu____13171)))
in (

let def_body1 = (norm cfg env1 [] def_body)
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____13228 = (

let uu___1686_13229 = rc
in (

let uu____13230 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env1 []))
in {FStar_Syntax_Syntax.residual_effect = uu___1686_13229.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____13230; FStar_Syntax_Syntax.residual_flags = uu___1686_13229.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____13228))
end
| uu____13239 -> begin
lopt
end)
in (

let def = (FStar_Syntax_Util.abs xs1 def_body1 lopt1)
in (

let uu___1691_13245 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___1691_13245.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___1691_13245.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___1691_13245.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1691_13245.FStar_Syntax_Syntax.lbpos}))))))
end))))) lbs1)
in (

let env' = (

let uu____13255 = (FStar_List.map (fun uu____13271 -> dummy) lbs2)
in (FStar_List.append uu____13255 env))
in (

let body2 = (norm cfg env' [] body1)
in (

let uu____13279 = (FStar_Syntax_Subst.close_let_rec lbs2 body2)
in (match (uu____13279) with
| (lbs3, body3) -> begin
(

let t2 = (

let uu___1700_13295 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (body3))); FStar_Syntax_Syntax.pos = uu___1700_13295.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___1700_13295.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack t2))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta)) -> begin
(

let uu____13329 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____13329))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let uu____13350 = (FStar_List.fold_right (fun lb uu____13428 -> (match (uu____13428) with
| (rec_env, memos, i) -> begin
(

let bv = (

let uu___1716_13553 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___1716_13553.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___1716_13553.FStar_Syntax_Syntax.sort})
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
in (match (uu____13350) with
| (rec_env, memos, uu____13744) -> begin
(

let uu____13799 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (FStar_Pervasives_Native.Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (FStar_Pervasives_Native.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env1 -> (

let uu____14048 = (

let uu____14055 = (

let uu____14056 = (

let uu____14088 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (uu____14088), (false)))
in Clos (uu____14056))
in ((FStar_Pervasives_Native.None), (uu____14055)))
in (uu____14048)::env1)) (FStar_Pervasives_Native.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head1, m) -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____14173 -> (

let uu____14174 = (FStar_Syntax_Print.metadata_to_string m)
in (FStar_Util.print1 ">> metadata = %s\n" uu____14174))));
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m1, t2) -> begin
(reduce_impure_comp cfg env stack head1 (FStar_Util.Inl (m1)) t2)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) -> begin
(reduce_impure_comp cfg env stack head1 (FStar_Util.Inr (((m1), (m')))) t2)
end
| uu____14198 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unmeta) with
| true -> begin
(norm cfg env stack head1)
end
| uu____14200 -> begin
(match (stack) with
| (uu____14202)::uu____14203 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____14208) -> begin
(norm cfg env ((Meta (((env), (m), (r))))::stack) head1)
end
| FStar_Syntax_Syntax.Meta_pattern (names1, args) -> begin
(

let args1 = (norm_pattern_args cfg env args)
in (

let names2 = (FStar_All.pipe_right names1 (FStar_List.map (norm cfg env [])))
in (norm cfg env ((Meta (((env), (FStar_Syntax_Syntax.Meta_pattern (((names2), (args1)))), (t1.FStar_Syntax_Syntax.pos))))::stack) head1)))
end
| uu____14287 -> begin
(norm cfg env stack head1)
end)
end
| [] -> begin
(

let head2 = (norm cfg env [] head1)
in (

let m1 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (names1, args) -> begin
(

let names2 = (FStar_All.pipe_right names1 (FStar_List.map (norm cfg env [])))
in (

let uu____14335 = (

let uu____14356 = (norm_pattern_args cfg env args)
in ((names2), (uu____14356)))
in FStar_Syntax_Syntax.Meta_pattern (uu____14335)))
end
| uu____14385 -> begin
m
end)
in (

let t2 = (mk (FStar_Syntax_Syntax.Tm_meta (((head2), (m1)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t2))))
end)
end)
end);
)
end
| FStar_Syntax_Syntax.Tm_delayed (uu____14391) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (norm cfg env stack t2))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____14415) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____14429) -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(

let uu____14443 = (

let uu____14445 = (FStar_Range.string_of_range t2.FStar_Syntax_Syntax.pos)
in (

let uu____14447 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "(%s) CheckNoUvars: Unexpected unification variable remains: %s" uu____14445 uu____14447)))
in (failwith uu____14443))
end
| uu____14450 -> begin
(

let uu____14452 = (inline_closure_env cfg env [] t2)
in (rebuild cfg env stack uu____14452))
end)
end
| uu____14453 -> begin
(norm cfg env stack t2)
end))
end);
)))
and do_unfold_fv : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.qninfo  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t0 qninfo f -> (

let uu____14462 = (FStar_TypeChecker_Env.lookup_definition_qninfo cfg.FStar_TypeChecker_Cfg.delta_level f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v qninfo)
in (match (uu____14462) with
| FStar_Pervasives_Native.None -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____14476 -> (

let uu____14477 = (FStar_Syntax_Print.fv_to_string f)
in (FStar_Util.print1 " >> Tm_fvar case 2 for %s\n" uu____14477))));
(rebuild cfg env stack t0);
)
end
| FStar_Pervasives_Native.Some (us, t) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____14490 -> (

let uu____14491 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____14493 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 " >> Unfolded %s to %s\n" uu____14491 uu____14493)))));
(

let t1 = (match ((Prims.op_Equality cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_until (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)))) with
| true -> begin
t
end
| uu____14500 -> begin
(FStar_Syntax_Subst.set_use_range t0.FStar_Syntax_Syntax.pos t)
end)
in (

let n1 = (FStar_List.length us)
in (match ((n1 > (Prims.parse_int "0"))) with
| true -> begin
(match (stack) with
| (UnivArgs (us', uu____14506))::stack1 -> begin
((

let uu____14515 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv) (FStar_Options.Other ("univ_norm")))
in (match (uu____14515) with
| true -> begin
(FStar_List.iter (fun x -> (

let uu____14523 = (FStar_Syntax_Print.univ_to_string x)
in (FStar_Util.print1 "Univ (normalizer) %s\n" uu____14523))) us')
end
| uu____14526 -> begin
()
end));
(

let env1 = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env1 u -> (((FStar_Pervasives_Native.None), (Univ (u))))::env1) env))
in (norm cfg env1 stack1 t1));
)
end
| uu____14559 when (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.erase_universes || cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.allow_unbound_universes) -> begin
(norm cfg env stack t1)
end
| uu____14562 -> begin
(

let uu____14565 = (

let uu____14567 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" uu____14567))
in (failwith uu____14565))
end)
end
| uu____14570 -> begin
(norm cfg env stack t1)
end)));
)
end)))
and reduce_impure_comp : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.monad_name, (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name)) FStar_Util.either  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun cfg env stack head1 m t -> (

let t1 = (norm cfg env [] t)
in (

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.pure_subterms_within_computations) with
| true -> begin
(

let new_steps = (FStar_TypeChecker_Env.PureSubtermsWithinComputations)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.Inlining)::[]
in (

let uu___1828_14595 = cfg
in (

let uu____14596 = (FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one new_steps cfg.FStar_TypeChecker_Cfg.steps)
in {FStar_TypeChecker_Cfg.steps = uu____14596; FStar_TypeChecker_Cfg.tcenv = uu___1828_14595.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1828_14595.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = (FStar_TypeChecker_Env.InliningDelta)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; FStar_TypeChecker_Cfg.primitive_steps = uu___1828_14595.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1828_14595.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1828_14595.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1828_14595.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1828_14595.FStar_TypeChecker_Cfg.reifying})))
end
| uu____14597 -> begin
cfg
end)
in (

let metadata = (match (m) with
| FStar_Util.Inl (m1) -> begin
FStar_Syntax_Syntax.Meta_monadic (((m1), (t1)))
end
| FStar_Util.Inr (m1, m') -> begin
FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t1)))
end)
in (norm cfg1 env ((Meta (((env), (metadata), (head1.FStar_Syntax_Syntax.pos))))::stack1) head1))))))
and do_reify_monadic : (unit  ->  FStar_Syntax_Syntax.term)  ->  FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun fallback cfg env stack head1 m t -> ((match (stack) with
| (App (uu____14627, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____14628; FStar_Syntax_Syntax.vars = uu____14629}, uu____14630, uu____14631))::uu____14632 -> begin
()
end
| uu____14637 -> begin
(

let uu____14640 = (

let uu____14642 = (stack_to_string stack)
in (FStar_Util.format1 "INTERNAL ERROR: do_reify_monadic: bad stack: %s" uu____14642))
in (failwith uu____14640))
end);
(

let head0 = head1
in (

let head2 = (FStar_Syntax_Util.unascribe head1)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____14651 -> (

let uu____14652 = (FStar_Syntax_Print.tag_of_term head2)
in (

let uu____14654 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print2 "Reifying: (%s) %s\n" uu____14652 uu____14654)))));
(

let head3 = (FStar_Syntax_Util.unmeta_safe head2)
in (

let uu____14658 = (

let uu____14659 = (FStar_Syntax_Subst.compress head3)
in uu____14659.FStar_Syntax_Syntax.n)
in (match (uu____14658) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (

let uu____14680 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv m)
in (FStar_TypeChecker_Env.get_effect_decl cfg.FStar_TypeChecker_Cfg.tcenv uu____14680))
in (

let uu____14681 = (

let uu____14690 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr)
in (FStar_All.pipe_right uu____14690 FStar_Util.must))
in (match (uu____14681) with
| (uu____14705, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____14715) -> begin
(failwith "Cannot reify a top-level let binding")
end
| FStar_Util.Inl (x) -> begin
(

let is_return = (fun e -> (

let uu____14726 = (

let uu____14727 = (FStar_Syntax_Subst.compress e)
in uu____14727.FStar_Syntax_Syntax.n)
in (match (uu____14726) with
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____14733, uu____14734)) -> begin
(

let uu____14743 = (

let uu____14744 = (FStar_Syntax_Subst.compress e1)
in uu____14744.FStar_Syntax_Syntax.n)
in (match (uu____14743) with
| FStar_Syntax_Syntax.Tm_meta (e2, FStar_Syntax_Syntax.Meta_monadic_lift (uu____14750, msrc, uu____14752)) when (FStar_Syntax_Util.is_pure_effect msrc) -> begin
(

let uu____14761 = (FStar_Syntax_Subst.compress e2)
in FStar_Pervasives_Native.Some (uu____14761))
end
| uu____14762 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____14763 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____14764 = (is_return lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____14764) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let lb1 = (

let uu___1900_14769 = lb
in {FStar_Syntax_Syntax.lbname = uu___1900_14769.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___1900_14769.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___1900_14769.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu___1900_14769.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1900_14769.FStar_Syntax_Syntax.lbpos})
in (

let uu____14770 = (FStar_List.tl stack)
in (

let uu____14771 = (

let uu____14772 = (

let uu____14779 = (

let uu____14780 = (

let uu____14794 = (FStar_Syntax_Util.mk_reify body)
in ((((false), ((lb1)::[]))), (uu____14794)))
in FStar_Syntax_Syntax.Tm_let (uu____14780))
in (FStar_Syntax_Syntax.mk uu____14779))
in (uu____14772 FStar_Pervasives_Native.None head3.FStar_Syntax_Syntax.pos))
in (norm cfg env uu____14770 uu____14771))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____14810 = (

let uu____14812 = (is_return body)
in (match (uu____14812) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_bvar (y); FStar_Syntax_Syntax.pos = uu____14817; FStar_Syntax_Syntax.vars = uu____14818}) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____14821 -> begin
false
end))
in (match (uu____14810) with
| true -> begin
(norm cfg env stack lb.FStar_Syntax_Syntax.lbdef)
end
| uu____14826 -> begin
(

let rng = head3.FStar_Syntax_Syntax.pos
in (

let head4 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body1 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify body)
in (

let body_rc = {FStar_Syntax_Syntax.residual_effect = m; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = []}
in (

let body2 = (

let uu____14845 = (

let uu____14852 = (

let uu____14853 = (

let uu____14872 = (

let uu____14881 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____14881)::[])
in ((uu____14872), (body1), (FStar_Pervasives_Native.Some (body_rc))))
in FStar_Syntax_Syntax.Tm_abs (uu____14853))
in (FStar_Syntax_Syntax.mk uu____14852))
in (uu____14845 FStar_Pervasives_Native.None body1.FStar_Syntax_Syntax.pos))
in (

let close1 = (closure_as_term cfg env)
in (

let bind_inst = (

let uu____14920 = (

let uu____14921 = (FStar_Syntax_Subst.compress bind_repr)
in uu____14921.FStar_Syntax_Syntax.n)
in (match (uu____14920) with
| FStar_Syntax_Syntax.Tm_uinst (bind1, (uu____14927)::(uu____14928)::[]) -> begin
(

let uu____14933 = (

let uu____14940 = (

let uu____14941 = (

let uu____14948 = (

let uu____14949 = (

let uu____14950 = (close1 lb.FStar_Syntax_Syntax.lbtyp)
in (cfg.FStar_TypeChecker_Cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.FStar_TypeChecker_Cfg.tcenv uu____14950))
in (

let uu____14951 = (

let uu____14954 = (

let uu____14955 = (close1 t)
in (cfg.FStar_TypeChecker_Cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.FStar_TypeChecker_Cfg.tcenv uu____14955))
in (uu____14954)::[])
in (uu____14949)::uu____14951))
in ((bind1), (uu____14948)))
in FStar_Syntax_Syntax.Tm_uinst (uu____14941))
in (FStar_Syntax_Syntax.mk uu____14940))
in (uu____14933 FStar_Pervasives_Native.None rng))
end
| uu____14958 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let maybe_range_arg = (

let uu____14973 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____14973) with
| true -> begin
(

let uu____14986 = (

let uu____14995 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range lb.FStar_Syntax_Syntax.lbpos lb.FStar_Syntax_Syntax.lbpos)
in (FStar_Syntax_Syntax.as_arg uu____14995))
in (

let uu____14996 = (

let uu____15007 = (

let uu____15016 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range body2.FStar_Syntax_Syntax.pos body2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.as_arg uu____15016))
in (uu____15007)::[])
in (uu____14986)::uu____14996))
end
| uu____15041 -> begin
[]
end))
in (

let reified = (

let args = (

let uu____15065 = (FStar_Syntax_Util.is_layered ed)
in (match (uu____15065) with
| true -> begin
(

let unit_args = (

let uu____15089 = (

let uu____15090 = (

let uu____15093 = (

let uu____15094 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_vc_combinator)
in (FStar_All.pipe_right uu____15094 FStar_Pervasives_Native.snd))
in (FStar_All.pipe_right uu____15093 FStar_Syntax_Subst.compress))
in uu____15090.FStar_Syntax_Syntax.n)
in (match (uu____15089) with
| FStar_Syntax_Syntax.Tm_arrow ((uu____15135)::(uu____15136)::bs, uu____15138) when ((FStar_List.length bs) >= (Prims.parse_int "2")) -> begin
(

let uu____15190 = (

let uu____15199 = (FStar_All.pipe_right bs (FStar_List.splitAt ((FStar_List.length bs) - (Prims.parse_int "2"))))
in (FStar_All.pipe_right uu____15199 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____15190 (FStar_List.map (fun uu____15330 -> (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.unit_const)))))
end
| uu____15337 -> begin
(

let uu____15338 = (

let uu____15344 = (

let uu____15346 = (FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let uu____15348 = (

let uu____15350 = (

let uu____15351 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_vc_combinator)
in (FStar_All.pipe_right uu____15351 FStar_Pervasives_Native.snd))
in (FStar_All.pipe_right uu____15350 FStar_Syntax_Print.term_to_string))
in (FStar_Util.format2 "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)" uu____15346 uu____15348)))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____15344)))
in (FStar_Errors.raise_error uu____15338 rng))
end))
in (

let uu____15385 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____15394 = (

let uu____15405 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____15414 = (

let uu____15425 = (

let uu____15436 = (FStar_Syntax_Syntax.as_arg head4)
in (

let uu____15445 = (

let uu____15456 = (FStar_Syntax_Syntax.as_arg body2)
in (uu____15456)::[])
in (uu____15436)::uu____15445))
in (FStar_List.append unit_args uu____15425))
in (uu____15405)::uu____15414))
in (uu____15385)::uu____15394)))
end
| uu____15513 -> begin
(

let uu____15515 = (

let uu____15526 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____15535 = (

let uu____15546 = (FStar_Syntax_Syntax.as_arg t)
in (uu____15546)::[])
in (uu____15526)::uu____15535))
in (

let uu____15579 = (

let uu____15590 = (

let uu____15601 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____15610 = (

let uu____15621 = (FStar_Syntax_Syntax.as_arg head4)
in (

let uu____15630 = (

let uu____15641 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____15650 = (

let uu____15661 = (FStar_Syntax_Syntax.as_arg body2)
in (uu____15661)::[])
in (uu____15641)::uu____15650))
in (uu____15621)::uu____15630))
in (uu____15601)::uu____15610))
in (FStar_List.append maybe_range_arg uu____15590))
in (FStar_List.append uu____15515 uu____15579)))
end))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((bind_inst), (args)))) FStar_Pervasives_Native.None rng))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____15742 -> (

let uu____15743 = (FStar_Syntax_Print.term_to_string head0)
in (

let uu____15745 = (FStar_Syntax_Print.term_to_string reified)
in (FStar_Util.print2 "Reified (1) <%s> to %s\n" uu____15743 uu____15745)))));
(

let uu____15748 = (FStar_List.tl stack)
in (norm cfg env uu____15748 reified));
))))))))))
end))
end)))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head_app, args) -> begin
((

let uu____15776 = (FStar_Options.defensive ())
in (match (uu____15776) with
| true -> begin
(

let is_arg_impure = (fun uu____15791 -> (match (uu____15791) with
| (e, q) -> begin
(

let uu____15805 = (

let uu____15806 = (FStar_Syntax_Subst.compress e)
in uu____15806.FStar_Syntax_Syntax.n)
in (match (uu____15805) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t')) -> begin
(

let uu____15822 = (FStar_Syntax_Util.is_pure_effect m1)
in (not (uu____15822)))
end
| uu____15824 -> begin
false
end))
end))
in (

let uu____15826 = (

let uu____15828 = (

let uu____15839 = (FStar_Syntax_Syntax.as_arg head_app)
in (uu____15839)::args)
in (FStar_Util.for_some is_arg_impure uu____15828))
in (match (uu____15826) with
| true -> begin
(

let uu____15865 = (

let uu____15871 = (

let uu____15873 = (FStar_Syntax_Print.term_to_string head3)
in (FStar_Util.format1 "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n" uu____15873))
in ((FStar_Errors.Warning_Defensive), (uu____15871)))
in (FStar_Errors.log_issue head3.FStar_Syntax_Syntax.pos uu____15865))
end
| uu____15877 -> begin
()
end)))
end
| uu____15879 -> begin
()
end));
(

let fallback1 = (fun uu____15886 -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____15890 -> (

let uu____15891 = (FStar_Syntax_Print.term_to_string head0)
in (FStar_Util.print2 "Reified (2) <%s> to %s\n" uu____15891 ""))));
(

let uu____15895 = (FStar_List.tl stack)
in (

let uu____15896 = (FStar_Syntax_Util.mk_reify head3)
in (norm cfg env uu____15895 uu____15896)));
))
in (

let fallback2 = (fun uu____15902 -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____15906 -> (

let uu____15907 = (FStar_Syntax_Print.term_to_string head0)
in (FStar_Util.print2 "Reified (3) <%s> to %s\n" uu____15907 ""))));
(

let uu____15911 = (FStar_List.tl stack)
in (

let uu____15912 = (mk (FStar_Syntax_Syntax.Tm_meta (((head3), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) head0.FStar_Syntax_Syntax.pos)
in (norm cfg env uu____15911 uu____15912)));
))
in (

let uu____15917 = (

let uu____15918 = (FStar_Syntax_Util.un_uinst head_app)
in uu____15918.FStar_Syntax_Syntax.n)
in (match (uu____15917) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let qninfo = (FStar_TypeChecker_Env.lookup_qname cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (

let uu____15924 = (

let uu____15926 = (FStar_TypeChecker_Env.is_action cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (not (uu____15926)))
in (match (uu____15924) with
| true -> begin
(fallback1 ())
end
| uu____15929 -> begin
(

let uu____15931 = (

let uu____15933 = (FStar_TypeChecker_Env.lookup_definition_qninfo cfg.FStar_TypeChecker_Cfg.delta_level fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v qninfo)
in (FStar_Option.isNone uu____15933))
in (match (uu____15931) with
| true -> begin
(fallback2 ())
end
| uu____15945 -> begin
(

let t1 = (

let uu____15950 = (

let uu____15955 = (FStar_Syntax_Util.mk_reify head_app)
in (FStar_Syntax_Syntax.mk_Tm_app uu____15955 args))
in (uu____15950 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let uu____15956 = (FStar_List.tl stack)
in (norm cfg env uu____15956 t1)))
end))
end))))
end
| uu____15957 -> begin
(fallback1 ())
end))));
)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (uu____15959)) -> begin
(do_reify_monadic fallback cfg env stack e m t)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (

let uu____15983 = (closure_as_term cfg env t')
in (reify_lift cfg e msrc mtgt uu____15983))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____15987 -> (

let uu____15988 = (FStar_Syntax_Print.term_to_string lifted)
in (FStar_Util.print1 "Reified lift to (2): %s\n" uu____15988))));
(

let uu____15991 = (FStar_List.tl stack)
in (norm cfg env uu____15991 lifted));
))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____16112 -> (match (uu____16112) with
| (pat, wopt, tm) -> begin
(

let uu____16160 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____16160)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches1)))) head3.FStar_Syntax_Syntax.pos)
in (

let uu____16192 = (FStar_List.tl stack)
in (norm cfg env uu____16192 tm))))
end
| uu____16193 -> begin
(fallback ())
end)));
)));
))
and reify_lift : FStar_TypeChecker_Cfg.cfg  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg e msrc mtgt t -> (

let env = cfg.FStar_TypeChecker_Cfg.tcenv
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____16207 -> (

let uu____16208 = (FStar_Ident.string_of_lid msrc)
in (

let uu____16210 = (FStar_Ident.string_of_lid mtgt)
in (

let uu____16212 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16208 uu____16210 uu____16212))))));
(

let uu____16215 = (((FStar_Syntax_Util.is_pure_effect msrc) || (FStar_Syntax_Util.is_div_effect msrc)) && (

let uu____16218 = (FStar_All.pipe_right mtgt (FStar_TypeChecker_Env.is_layered_effect env))
in (not (uu____16218))))
in (match (uu____16215) with
| true -> begin
(

let ed = (

let uu____16223 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv mtgt)
in (FStar_TypeChecker_Env.get_effect_decl env uu____16223))
in (

let uu____16224 = (

let uu____16231 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr)
in (FStar_All.pipe_right uu____16231 FStar_Util.must))
in (match (uu____16224) with
| (uu____16268, return_repr) -> begin
(

let return_inst = (

let uu____16277 = (

let uu____16278 = (FStar_Syntax_Subst.compress return_repr)
in uu____16278.FStar_Syntax_Syntax.n)
in (match (uu____16277) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (uu____16284)::[]) -> begin
(

let uu____16289 = (

let uu____16296 = (

let uu____16297 = (

let uu____16304 = (

let uu____16305 = (env.FStar_TypeChecker_Env.universe_of env t)
in (uu____16305)::[])
in ((return_tm), (uu____16304)))
in FStar_Syntax_Syntax.Tm_uinst (uu____16297))
in (FStar_Syntax_Syntax.mk uu____16296))
in (uu____16289 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end
| uu____16308 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let uu____16312 = (

let uu____16319 = (

let uu____16320 = (

let uu____16337 = (

let uu____16348 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____16357 = (

let uu____16368 = (FStar_Syntax_Syntax.as_arg e)
in (uu____16368)::[])
in (uu____16348)::uu____16357))
in ((return_inst), (uu____16337)))
in FStar_Syntax_Syntax.Tm_app (uu____16320))
in (FStar_Syntax_Syntax.mk uu____16319))
in (uu____16312 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end)))
end
| uu____16413 -> begin
(

let uu____16415 = (FStar_TypeChecker_Env.monad_leq env msrc mtgt)
in (match (uu____16415) with
| FStar_Pervasives_Native.None -> begin
(

let uu____16418 = (

let uu____16420 = (FStar_Ident.text_of_lid msrc)
in (

let uu____16422 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" uu____16420 uu____16422)))
in (failwith uu____16418))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____16425; FStar_TypeChecker_Env.mtarget = uu____16426; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____16427; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(

let uu____16447 = (

let uu____16449 = (FStar_Ident.text_of_lid msrc)
in (

let uu____16451 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a non-reifiable lift (from %s to %s)" uu____16449 uu____16451)))
in (failwith uu____16447))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____16454; FStar_TypeChecker_Env.mtarget = uu____16455; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____16456; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let e1 = (

let uu____16487 = (FStar_TypeChecker_Env.is_reifiable_effect env msrc)
in (match (uu____16487) with
| true -> begin
(FStar_Syntax_Util.mk_reify e)
end
| uu____16490 -> begin
(

let uu____16492 = (

let uu____16499 = (

let uu____16500 = (

let uu____16519 = (

let uu____16528 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_unit)
in (uu____16528)::[])
in ((uu____16519), (e), (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.residual_effect = msrc; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = []}))))
in FStar_Syntax_Syntax.Tm_abs (uu____16500))
in (FStar_Syntax_Syntax.mk uu____16499))
in (uu____16492 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end))
in (

let uu____16561 = (env.FStar_TypeChecker_Env.universe_of env t)
in (lift uu____16561 t e1)))
end))
end));
)))
and norm_pattern_args : FStar_TypeChecker_Cfg.cfg  ->  env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun uu____16631 -> (match (uu____16631) with
| (a, imp) -> begin
(

let uu____16650 = (norm cfg env [] a)
in ((uu____16650), (imp)))
end))))))
and norm_comp : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____16660 -> (

let uu____16661 = (FStar_Syntax_Print.comp_to_string comp)
in (

let uu____16663 = (FStar_Util.string_of_int (FStar_List.length env))
in (FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n" uu____16661 uu____16663)))));
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let t1 = (norm cfg env [] t)
in (

let uopt1 = (match (uopt) with
| FStar_Pervasives_Native.Some (u) -> begin
(

let uu____16689 = (norm_universe cfg env u)
in (FStar_All.pipe_left (fun _16692 -> FStar_Pervasives_Native.Some (_16692)) uu____16689))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let uu___2065_16693 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t1), (uopt1))); FStar_Syntax_Syntax.pos = uu___2065_16693.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___2065_16693.FStar_Syntax_Syntax.vars})))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let t1 = (norm cfg env [] t)
in (

let uopt1 = (match (uopt) with
| FStar_Pervasives_Native.Some (u) -> begin
(

let uu____16715 = (norm_universe cfg env u)
in (FStar_All.pipe_left (fun _16718 -> FStar_Pervasives_Native.Some (_16718)) uu____16715))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let uu___2076_16719 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (((t1), (uopt1))); FStar_Syntax_Syntax.pos = uu___2076_16719.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___2076_16719.FStar_Syntax_Syntax.vars})))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (FStar_List.mapi (fun idx uu____16764 -> (match (uu____16764) with
| (a, i) -> begin
(

let uu____16784 = (norm cfg env [] a)
in ((uu____16784), (i)))
end)))
in (

let effect_args = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___14_16806 -> (match (uu___14_16806) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____16810 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____16810))
end
| f -> begin
f
end))))
in (

let comp_univs = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (

let result_typ = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (

let uu___2093_16818 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ((

let uu___2095_16821 = ct
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___2095_16821.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = effect_args; FStar_Syntax_Syntax.flags = flags})); FStar_Syntax_Syntax.pos = uu___2093_16818.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___2093_16818.FStar_Syntax_Syntax.vars}))))))
end);
))
and norm_binder : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env b -> (

let uu____16825 = b
in (match (uu____16825) with
| (x, imp) -> begin
(

let x1 = (

let uu___2103_16833 = x
in (

let uu____16834 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___2103_16833.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2103_16833.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____16834}))
in (

let imp1 = (match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____16845 = (

let uu____16846 = (closure_as_term cfg env t)
in FStar_Syntax_Syntax.Meta (uu____16846))
in FStar_Pervasives_Native.Some (uu____16845))
end
| i -> begin
i
end)
in ((x1), (imp1))))
end)))
and norm_binders : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let uu____16857 = (FStar_List.fold_left (fun uu____16891 b -> (match (uu____16891) with
| (nbs', env1) -> begin
(

let b1 = (norm_binder cfg env1 b)
in (((b1)::nbs'), ((dummy)::env1)))
end)) (([]), (env)) bs)
in (match (uu____16857) with
| (nbs, uu____16971) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags = (filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags)
in (

let uu____17003 = (

let uu___2128_17004 = rc
in (

let uu____17005 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___2128_17004.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____17005; FStar_Syntax_Syntax.residual_flags = uu___2128_17004.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____17003)))
end
| uu____17014 -> begin
lopt
end))
and maybe_simplify : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack tm -> (

let tm' = (maybe_simplify_aux cfg env stack tm)
in ((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.b380) with
| true -> begin
(

let uu____17024 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____17026 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n" (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.simplify) with
| true -> begin
""
end
| uu____17032 -> begin
"NOT "
end) uu____17024 uu____17026)))
end
| uu____17035 -> begin
()
end);
tm';
)))
and norm_cb : FStar_TypeChecker_Cfg.cfg  ->  FStar_Syntax_Embeddings.norm_cb = (fun cfg uu___15_17038 -> (match (uu___15_17038) with
| FStar_Util.Inr (x) -> begin
(norm cfg [] [] x)
end
| FStar_Util.Inl (l) -> begin
(

let uu____17051 = (FStar_Syntax_DsEnv.try_lookup_lid cfg.FStar_TypeChecker_Cfg.tcenv.FStar_TypeChecker_Env.dsenv l)
in (match (uu____17051) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____17055 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____17055))
end))
end))
and maybe_simplify_aux : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack tm -> (

let tm1 = (

let uu____17063 = (norm_cb cfg)
in (reduce_primops uu____17063 cfg env tm))
in (

let uu____17068 = (FStar_All.pipe_left Prims.op_Negation cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.simplify)
in (match (uu____17068) with
| true -> begin
tm1
end
| uu____17073 -> begin
(

let w = (fun t -> (

let uu___2156_17087 = t
in {FStar_Syntax_Syntax.n = uu___2156_17087.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = tm1.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___2156_17087.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (

let uu____17099 = (

let uu____17100 = (FStar_Syntax_Util.unmeta t)
in uu____17100.FStar_Syntax_Syntax.n)
in (match (uu____17099) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_Pervasives_Native.Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid) -> begin
FStar_Pervasives_Native.Some (false)
end
| uu____17112 -> begin
FStar_Pervasives_Native.None
end)))
in (

let rec args_are_binders = (fun args bs -> (match (((args), (bs))) with
| (((t, uu____17176))::args1, ((bv, uu____17179))::bs1) -> begin
(

let uu____17233 = (

let uu____17234 = (FStar_Syntax_Subst.compress t)
in uu____17234.FStar_Syntax_Syntax.n)
in (match (uu____17233) with
| FStar_Syntax_Syntax.Tm_name (bv') -> begin
((FStar_Syntax_Syntax.bv_eq bv bv') && (args_are_binders args1 bs1))
end
| uu____17239 -> begin
false
end))
end
| ([], []) -> begin
true
end
| (uu____17270, uu____17271) -> begin
false
end))
in (

let is_applied = (fun bs t -> ((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____17322 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____17324 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17322 uu____17324)))
end
| uu____17327 -> begin
()
end);
(

let uu____17329 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____17329) with
| (hd1, args) -> begin
(

let uu____17368 = (

let uu____17369 = (FStar_Syntax_Subst.compress hd1)
in uu____17369.FStar_Syntax_Syntax.n)
in (match (uu____17368) with
| FStar_Syntax_Syntax.Tm_name (bv) when (args_are_binders args bs) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____17377 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____17379 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____17381 = (FStar_Syntax_Print.term_to_string hd1)
in (FStar_Util.print3 "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n" uu____17377 uu____17379 uu____17381))))
end
| uu____17384 -> begin
()
end);
FStar_Pervasives_Native.Some (bv);
)
end
| uu____17386 -> begin
FStar_Pervasives_Native.None
end))
end));
))
in (

let is_applied_maybe_squashed = (fun bs t -> ((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____17404 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____17406 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17404 uu____17406)))
end
| uu____17409 -> begin
()
end);
(

let uu____17411 = (FStar_Syntax_Util.is_squash t)
in (match (uu____17411) with
| FStar_Pervasives_Native.Some (uu____17422, t') -> begin
(is_applied bs t')
end
| uu____17434 -> begin
(

let uu____17443 = (FStar_Syntax_Util.is_auto_squash t)
in (match (uu____17443) with
| FStar_Pervasives_Native.Some (uu____17454, t') -> begin
(is_applied bs t')
end
| uu____17466 -> begin
(is_applied bs t)
end))
end));
))
in (

let is_quantified_const = (fun bv phi -> (

let uu____17490 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____17490) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid, ((p, uu____17497))::((q, uu____17499))::[])) when (FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____17542 = (FStar_Syntax_Print.term_to_string p)
in (

let uu____17544 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print2 "WPE> p = (%s); q = (%s)\n" uu____17542 uu____17544)))
end
| uu____17547 -> begin
()
end);
(

let uu____17549 = (FStar_Syntax_Util.destruct_typ_as_formula p)
in (match (uu____17549) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17554 = (

let uu____17555 = (FStar_Syntax_Subst.compress p)
in uu____17555.FStar_Syntax_Syntax.n)
in (match (uu____17554) with
| FStar_Syntax_Syntax.Tm_bvar (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 1\n")
end
| uu____17564 -> begin
()
end);
(

let uu____17566 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (FStar_Syntax_Util.t_true))))::[]) q)
in FStar_Pervasives_Native.Some (uu____17566));
)
end
| uu____17569 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid1, ((p1, uu____17572))::[])) when (FStar_Ident.lid_equals lid1 FStar_Parser_Const.not_lid) -> begin
(

let uu____17597 = (

let uu____17598 = (FStar_Syntax_Subst.compress p1)
in uu____17598.FStar_Syntax_Syntax.n)
in (match (uu____17597) with
| FStar_Syntax_Syntax.Tm_bvar (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 2\n")
end
| uu____17607 -> begin
()
end);
(

let uu____17609 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (FStar_Syntax_Util.t_false))))::[]) q)
in FStar_Pervasives_Native.Some (uu____17609));
)
end
| uu____17612 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (bs, pats, phi1)) -> begin
(

let uu____17616 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____17616) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17621 = (is_applied_maybe_squashed bs phi1)
in (match (uu____17621) with
| FStar_Pervasives_Native.Some (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 3\n")
end
| uu____17630 -> begin
()
end);
(

let ftrue = (FStar_Syntax_Util.abs bs FStar_Syntax_Util.t_true (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let uu____17635 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (ftrue))))::[]) q)
in FStar_Pervasives_Native.Some (uu____17635)));
)
end
| uu____17638 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid1, ((p1, uu____17643))::[])) when (FStar_Ident.lid_equals lid1 FStar_Parser_Const.not_lid) -> begin
(

let uu____17668 = (is_applied_maybe_squashed bs p1)
in (match (uu____17668) with
| FStar_Pervasives_Native.Some (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 4\n")
end
| uu____17677 -> begin
()
end);
(

let ffalse = (FStar_Syntax_Util.abs bs FStar_Syntax_Util.t_false (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let uu____17682 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (ffalse))))::[]) q)
in FStar_Pervasives_Native.Some (uu____17682)));
)
end
| uu____17685 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____17688 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____17691 -> begin
FStar_Pervasives_Native.None
end));
)
end
| uu____17694 -> begin
FStar_Pervasives_Native.None
end)))
in (

let is_forall_const = (fun phi -> (

let uu____17707 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____17707) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (((bv, uu____17713))::[], uu____17714, phi')) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____17734 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____17736 = (FStar_Syntax_Print.term_to_string phi')
in (FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____17734 uu____17736)))
end
| uu____17739 -> begin
()
end);
(is_quantified_const bv phi');
)
end
| uu____17741 -> begin
FStar_Pervasives_Native.None
end)))
in (

let is_const_match = (fun phi -> (

let uu____17756 = (

let uu____17757 = (FStar_Syntax_Subst.compress phi)
in uu____17757.FStar_Syntax_Syntax.n)
in (match (uu____17756) with
| FStar_Syntax_Syntax.Tm_match (uu____17763, (br)::brs) -> begin
(

let uu____17830 = br
in (match (uu____17830) with
| (uu____17848, uu____17849, e) -> begin
(

let r = (

let uu____17871 = (simp_t e)
in (match (uu____17871) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let uu____17883 = (FStar_List.for_all (fun uu____17902 -> (match (uu____17902) with
| (uu____17916, uu____17917, e') -> begin
(

let uu____17931 = (simp_t e')
in (Prims.op_Equality uu____17931 (FStar_Pervasives_Native.Some (b))))
end)) brs)
in (match (uu____17883) with
| true -> begin
FStar_Pervasives_Native.Some (b)
end
| uu____17944 -> begin
FStar_Pervasives_Native.None
end))
end))
in r)
end))
end
| uu____17947 -> begin
FStar_Pervasives_Native.None
end)))
in (

let maybe_auto_squash = (fun t -> (

let uu____17957 = (FStar_Syntax_Util.is_sub_singleton t)
in (match (uu____17957) with
| true -> begin
t
end
| uu____17962 -> begin
(FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t)
end)))
in (

let squashed_head_un_auto_squash_args = (fun t -> (

let maybe_un_auto_squash_arg = (fun uu____17995 -> (match (uu____17995) with
| (t1, q) -> begin
(

let uu____18016 = (FStar_Syntax_Util.is_auto_squash t1)
in (match (uu____18016) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t2) -> begin
((t2), (q))
end
| uu____18048 -> begin
((t1), (q))
end))
end))
in (

let uu____18061 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____18061) with
| (head1, args) -> begin
(

let args1 = (FStar_List.map maybe_un_auto_squash_arg args)
in (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))))
in (

let rec clearly_inhabited = (fun ty -> (

let uu____18141 = (

let uu____18142 = (FStar_Syntax_Util.unmeta ty)
in uu____18142.FStar_Syntax_Syntax.n)
in (match (uu____18141) with
| FStar_Syntax_Syntax.Tm_uinst (t, uu____18147) -> begin
(clearly_inhabited t)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____18152, c) -> begin
(clearly_inhabited (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in ((((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)))
end
| uu____18176 -> begin
false
end)))
in (

let simplify1 = (fun arg -> (

let uu____18209 = (simp_t (FStar_Pervasives_Native.fst arg))
in ((uu____18209), (arg))))
in (

let uu____18224 = (is_forall_const tm1)
in (match (uu____18224) with
| FStar_Pervasives_Native.Some (tm') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____18230 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____18232 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "WPE> %s ~> %s\n" uu____18230 uu____18232)))
end
| uu____18235 -> begin
()
end);
(

let uu____18237 = (norm cfg env [] tm')
in (maybe_simplify_aux cfg env stack uu____18237));
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____18238 = (

let uu____18239 = (FStar_Syntax_Subst.compress tm1)
in uu____18239.FStar_Syntax_Syntax.n)
in (match (uu____18238) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____18243; FStar_Syntax_Syntax.vars = uu____18244}, uu____18245); FStar_Syntax_Syntax.pos = uu____18246; FStar_Syntax_Syntax.vars = uu____18247}, args) -> begin
(

let uu____18277 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____18277) with
| true -> begin
(

let uu____18280 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____18280) with
| ((FStar_Pervasives_Native.Some (true), uu____18338))::((uu____18339, (arg, uu____18341)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____18414, (arg, uu____18416)))::((FStar_Pervasives_Native.Some (true), uu____18417))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (false), uu____18490))::(uu____18491)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____18561)::((FStar_Pervasives_Native.Some (false), uu____18562))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____18632 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____18648 -> begin
(

let uu____18650 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____18650) with
| true -> begin
(

let uu____18653 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____18653) with
| ((FStar_Pervasives_Native.Some (true), uu____18711))::(uu____18712)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____18782)::((FStar_Pervasives_Native.Some (true), uu____18783))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____18853))::((uu____18854, (arg, uu____18856)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____18929, (arg, uu____18931)))::((FStar_Pervasives_Native.Some (false), uu____18932))::[] -> begin
(maybe_auto_squash arg)
end
| uu____19005 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19021 -> begin
(

let uu____19023 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____19023) with
| true -> begin
(

let uu____19026 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____19026) with
| (uu____19084)::((FStar_Pervasives_Native.Some (true), uu____19085))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____19155))::(uu____19156)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____19226))::((uu____19227, (arg, uu____19229)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____19302, (p, uu____19304)))::((uu____19305, (q, uu____19307)))::[] -> begin
(

let uu____19379 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____19379) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____19382 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19384 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19400 -> begin
(

let uu____19402 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)
in (match (uu____19402) with
| true -> begin
(

let uu____19405 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____19405) with
| ((FStar_Pervasives_Native.Some (true), uu____19463))::((FStar_Pervasives_Native.Some (true), uu____19464))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____19538))::((FStar_Pervasives_Native.Some (false), uu____19539))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____19613))::((FStar_Pervasives_Native.Some (false), uu____19614))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____19688))::((FStar_Pervasives_Native.Some (true), uu____19689))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((uu____19763, (arg, uu____19765)))::((FStar_Pervasives_Native.Some (true), uu____19766))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (true), uu____19839))::((uu____19840, (arg, uu____19842)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____19915, (arg, uu____19917)))::((FStar_Pervasives_Native.Some (false), uu____19918))::[] -> begin
(

let uu____19991 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____19991))
end
| ((FStar_Pervasives_Native.Some (false), uu____19992))::((uu____19993, (arg, uu____19995)))::[] -> begin
(

let uu____20068 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____20068))
end
| ((uu____20069, (p, uu____20071)))::((uu____20072, (q, uu____20074)))::[] -> begin
(

let uu____20146 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____20146) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20149 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20151 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20167 -> begin
(

let uu____20169 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____20169) with
| true -> begin
(

let uu____20172 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____20172) with
| ((FStar_Pervasives_Native.Some (true), uu____20230))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____20274))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20318 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20334 -> begin
(

let uu____20336 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____20336) with
| true -> begin
(match (args) with
| ((t, uu____20340))::[] -> begin
(

let uu____20365 = (

let uu____20366 = (FStar_Syntax_Subst.compress t)
in uu____20366.FStar_Syntax_Syntax.n)
in (match (uu____20365) with
| FStar_Syntax_Syntax.Tm_abs ((uu____20369)::[], body, uu____20371) -> begin
(

let uu____20406 = (simp_t body)
in (match (uu____20406) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20412 -> begin
tm1
end))
end
| uu____20416 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____20418))))::((t, uu____20420))::[] -> begin
(

let uu____20460 = (

let uu____20461 = (FStar_Syntax_Subst.compress t)
in uu____20461.FStar_Syntax_Syntax.n)
in (match (uu____20460) with
| FStar_Syntax_Syntax.Tm_abs ((uu____20464)::[], body, uu____20466) -> begin
(

let uu____20501 = (simp_t body)
in (match (uu____20501) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| FStar_Pervasives_Native.Some (false) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____20509 -> begin
tm1
end))
end
| uu____20513 -> begin
tm1
end))
end
| uu____20514 -> begin
tm1
end)
end
| uu____20525 -> begin
(

let uu____20527 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____20527) with
| true -> begin
(match (args) with
| ((t, uu____20531))::[] -> begin
(

let uu____20556 = (

let uu____20557 = (FStar_Syntax_Subst.compress t)
in uu____20557.FStar_Syntax_Syntax.n)
in (match (uu____20556) with
| FStar_Syntax_Syntax.Tm_abs ((uu____20560)::[], body, uu____20562) -> begin
(

let uu____20597 = (simp_t body)
in (match (uu____20597) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____20603 -> begin
tm1
end))
end
| uu____20607 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____20609))))::((t, uu____20611))::[] -> begin
(

let uu____20651 = (

let uu____20652 = (FStar_Syntax_Subst.compress t)
in uu____20652.FStar_Syntax_Syntax.n)
in (match (uu____20651) with
| FStar_Syntax_Syntax.Tm_abs ((uu____20655)::[], body, uu____20657) -> begin
(

let uu____20692 = (simp_t body)
in (match (uu____20692) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| FStar_Pervasives_Native.Some (true) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20700 -> begin
tm1
end))
end
| uu____20704 -> begin
tm1
end))
end
| uu____20705 -> begin
tm1
end)
end
| uu____20716 -> begin
(

let uu____20718 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
in (match (uu____20718) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____20721; FStar_Syntax_Syntax.vars = uu____20722}, uu____20723))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____20749; FStar_Syntax_Syntax.vars = uu____20750}, uu____20751))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____20777 -> begin
tm1
end)
end
| uu____20788 -> begin
(

let uu____20790 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.haseq_lid)
in (match (uu____20790) with
| true -> begin
(

let t_has_eq_for_sure = (fun t -> (

let haseq_lids = (FStar_Parser_Const.int_lid)::(FStar_Parser_Const.bool_lid)::(FStar_Parser_Const.unit_lid)::(FStar_Parser_Const.string_lid)::[]
in (

let uu____20804 = (

let uu____20805 = (FStar_Syntax_Subst.compress t)
in uu____20805.FStar_Syntax_Syntax.n)
in (match (uu____20804) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (FStar_All.pipe_right haseq_lids (FStar_List.existsb (fun l -> (FStar_Syntax_Syntax.fv_eq_lid fv1 l)))) -> begin
true
end
| uu____20816 -> begin
false
end))))
in (match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "1"))) with
| true -> begin
(

let t = (

let uu____20830 = (FStar_All.pipe_right args FStar_List.hd)
in (FStar_All.pipe_right uu____20830 FStar_Pervasives_Native.fst))
in (

let uu____20869 = (FStar_All.pipe_right t t_has_eq_for_sure)
in (match (uu____20869) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20873 -> begin
(

let uu____20875 = (

let uu____20876 = (FStar_Syntax_Subst.compress t)
in uu____20876.FStar_Syntax_Syntax.n)
in (match (uu____20875) with
| FStar_Syntax_Syntax.Tm_refine (uu____20879) -> begin
(

let t1 = (FStar_Syntax_Util.unrefine t)
in (

let uu____20887 = (FStar_All.pipe_right t1 t_has_eq_for_sure)
in (match (uu____20887) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20891 -> begin
(

let haseq_tm = (

let uu____20896 = (

let uu____20897 = (FStar_Syntax_Subst.compress tm1)
in uu____20897.FStar_Syntax_Syntax.n)
in (match (uu____20896) with
| FStar_Syntax_Syntax.Tm_app (hd1, uu____20903) -> begin
hd1
end
| uu____20928 -> begin
(failwith "Impossible! We have already checked that this is a Tm_app")
end))
in (

let uu____20932 = (

let uu____20943 = (FStar_All.pipe_right t1 FStar_Syntax_Syntax.as_arg)
in (uu____20943)::[])
in (FStar_Syntax_Util.mk_app haseq_tm uu____20932)))
end)))
end
| uu____20976 -> begin
tm1
end))
end)))
end
| uu____20977 -> begin
tm1
end))
end
| uu____20979 -> begin
(

let uu____20981 = (FStar_Syntax_Util.is_auto_squash tm1)
in (match (uu____20981) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t) when (FStar_Syntax_Util.is_sub_singleton t) -> begin
t
end
| uu____21001 -> begin
(

let uu____21010 = (

let uu____21017 = (norm_cb cfg)
in (reduce_equality uu____21017 cfg env))
in (uu____21010 tm1))
end))
end))
end))
end))
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____21023; FStar_Syntax_Syntax.vars = uu____21024}, args) -> begin
(

let uu____21050 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____21050) with
| true -> begin
(

let uu____21053 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____21053) with
| ((FStar_Pervasives_Native.Some (true), uu____21111))::((uu____21112, (arg, uu____21114)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____21187, (arg, uu____21189)))::((FStar_Pervasives_Native.Some (true), uu____21190))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (false), uu____21263))::(uu____21264)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____21334)::((FStar_Pervasives_Native.Some (false), uu____21335))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____21405 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____21421 -> begin
(

let uu____21423 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____21423) with
| true -> begin
(

let uu____21426 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____21426) with
| ((FStar_Pervasives_Native.Some (true), uu____21484))::(uu____21485)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____21555)::((FStar_Pervasives_Native.Some (true), uu____21556))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____21626))::((uu____21627, (arg, uu____21629)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____21702, (arg, uu____21704)))::((FStar_Pervasives_Native.Some (false), uu____21705))::[] -> begin
(maybe_auto_squash arg)
end
| uu____21778 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____21794 -> begin
(

let uu____21796 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____21796) with
| true -> begin
(

let uu____21799 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____21799) with
| (uu____21857)::((FStar_Pervasives_Native.Some (true), uu____21858))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____21928))::(uu____21929)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____21999))::((uu____22000, (arg, uu____22002)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____22075, (p, uu____22077)))::((uu____22078, (q, uu____22080)))::[] -> begin
(

let uu____22152 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____22152) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22155 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____22157 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____22173 -> begin
(

let uu____22175 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)
in (match (uu____22175) with
| true -> begin
(

let uu____22178 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____22178) with
| ((FStar_Pervasives_Native.Some (true), uu____22236))::((FStar_Pervasives_Native.Some (true), uu____22237))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____22311))::((FStar_Pervasives_Native.Some (false), uu____22312))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____22386))::((FStar_Pervasives_Native.Some (false), uu____22387))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____22461))::((FStar_Pervasives_Native.Some (true), uu____22462))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((uu____22536, (arg, uu____22538)))::((FStar_Pervasives_Native.Some (true), uu____22539))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (true), uu____22612))::((uu____22613, (arg, uu____22615)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____22688, (arg, uu____22690)))::((FStar_Pervasives_Native.Some (false), uu____22691))::[] -> begin
(

let uu____22764 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____22764))
end
| ((FStar_Pervasives_Native.Some (false), uu____22765))::((uu____22766, (arg, uu____22768)))::[] -> begin
(

let uu____22841 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____22841))
end
| ((uu____22842, (p, uu____22844)))::((uu____22845, (q, uu____22847)))::[] -> begin
(

let uu____22919 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____22919) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22922 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____22924 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____22940 -> begin
(

let uu____22942 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____22942) with
| true -> begin
(

let uu____22945 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____22945) with
| ((FStar_Pervasives_Native.Some (true), uu____23003))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____23047))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____23091 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____23107 -> begin
(

let uu____23109 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____23109) with
| true -> begin
(match (args) with
| ((t, uu____23113))::[] -> begin
(

let uu____23138 = (

let uu____23139 = (FStar_Syntax_Subst.compress t)
in uu____23139.FStar_Syntax_Syntax.n)
in (match (uu____23138) with
| FStar_Syntax_Syntax.Tm_abs ((uu____23142)::[], body, uu____23144) -> begin
(

let uu____23179 = (simp_t body)
in (match (uu____23179) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____23185 -> begin
tm1
end))
end
| uu____23189 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____23191))))::((t, uu____23193))::[] -> begin
(

let uu____23233 = (

let uu____23234 = (FStar_Syntax_Subst.compress t)
in uu____23234.FStar_Syntax_Syntax.n)
in (match (uu____23233) with
| FStar_Syntax_Syntax.Tm_abs ((uu____23237)::[], body, uu____23239) -> begin
(

let uu____23274 = (simp_t body)
in (match (uu____23274) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| FStar_Pervasives_Native.Some (false) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____23282 -> begin
tm1
end))
end
| uu____23286 -> begin
tm1
end))
end
| uu____23287 -> begin
tm1
end)
end
| uu____23298 -> begin
(

let uu____23300 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____23300) with
| true -> begin
(match (args) with
| ((t, uu____23304))::[] -> begin
(

let uu____23329 = (

let uu____23330 = (FStar_Syntax_Subst.compress t)
in uu____23330.FStar_Syntax_Syntax.n)
in (match (uu____23329) with
| FStar_Syntax_Syntax.Tm_abs ((uu____23333)::[], body, uu____23335) -> begin
(

let uu____23370 = (simp_t body)
in (match (uu____23370) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____23376 -> begin
tm1
end))
end
| uu____23380 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____23382))))::((t, uu____23384))::[] -> begin
(

let uu____23424 = (

let uu____23425 = (FStar_Syntax_Subst.compress t)
in uu____23425.FStar_Syntax_Syntax.n)
in (match (uu____23424) with
| FStar_Syntax_Syntax.Tm_abs ((uu____23428)::[], body, uu____23430) -> begin
(

let uu____23465 = (simp_t body)
in (match (uu____23465) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| FStar_Pervasives_Native.Some (true) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____23473 -> begin
tm1
end))
end
| uu____23477 -> begin
tm1
end))
end
| uu____23478 -> begin
tm1
end)
end
| uu____23489 -> begin
(

let uu____23491 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
in (match (uu____23491) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____23494; FStar_Syntax_Syntax.vars = uu____23495}, uu____23496))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____23522; FStar_Syntax_Syntax.vars = uu____23523}, uu____23524))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____23550 -> begin
tm1
end)
end
| uu____23561 -> begin
(

let uu____23563 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.haseq_lid)
in (match (uu____23563) with
| true -> begin
(

let t_has_eq_for_sure = (fun t -> (

let haseq_lids = (FStar_Parser_Const.int_lid)::(FStar_Parser_Const.bool_lid)::(FStar_Parser_Const.unit_lid)::(FStar_Parser_Const.string_lid)::[]
in (

let uu____23577 = (

let uu____23578 = (FStar_Syntax_Subst.compress t)
in uu____23578.FStar_Syntax_Syntax.n)
in (match (uu____23577) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (FStar_All.pipe_right haseq_lids (FStar_List.existsb (fun l -> (FStar_Syntax_Syntax.fv_eq_lid fv1 l)))) -> begin
true
end
| uu____23589 -> begin
false
end))))
in (match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "1"))) with
| true -> begin
(

let t = (

let uu____23603 = (FStar_All.pipe_right args FStar_List.hd)
in (FStar_All.pipe_right uu____23603 FStar_Pervasives_Native.fst))
in (

let uu____23638 = (FStar_All.pipe_right t t_has_eq_for_sure)
in (match (uu____23638) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____23642 -> begin
(

let uu____23644 = (

let uu____23645 = (FStar_Syntax_Subst.compress t)
in uu____23645.FStar_Syntax_Syntax.n)
in (match (uu____23644) with
| FStar_Syntax_Syntax.Tm_refine (uu____23648) -> begin
(

let t1 = (FStar_Syntax_Util.unrefine t)
in (

let uu____23656 = (FStar_All.pipe_right t1 t_has_eq_for_sure)
in (match (uu____23656) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____23660 -> begin
(

let haseq_tm = (

let uu____23665 = (

let uu____23666 = (FStar_Syntax_Subst.compress tm1)
in uu____23666.FStar_Syntax_Syntax.n)
in (match (uu____23665) with
| FStar_Syntax_Syntax.Tm_app (hd1, uu____23672) -> begin
hd1
end
| uu____23697 -> begin
(failwith "Impossible! We have already checked that this is a Tm_app")
end))
in (

let uu____23701 = (

let uu____23712 = (FStar_All.pipe_right t1 FStar_Syntax_Syntax.as_arg)
in (uu____23712)::[])
in (FStar_Syntax_Util.mk_app haseq_tm uu____23701)))
end)))
end
| uu____23745 -> begin
tm1
end))
end)))
end
| uu____23746 -> begin
tm1
end))
end
| uu____23748 -> begin
(

let uu____23750 = (FStar_Syntax_Util.is_auto_squash tm1)
in (match (uu____23750) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t) when (FStar_Syntax_Util.is_sub_singleton t) -> begin
t
end
| uu____23770 -> begin
(

let uu____23779 = (

let uu____23786 = (norm_cb cfg)
in (reduce_equality uu____23786 cfg env))
in (uu____23779 tm1))
end))
end))
end))
end))
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let uu____23797 = (simp_t t)
in (match (uu____23797) with
| FStar_Pervasives_Native.Some (true) -> begin
bv.FStar_Syntax_Syntax.sort
end
| FStar_Pervasives_Native.Some (false) -> begin
tm1
end
| FStar_Pervasives_Native.None -> begin
tm1
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____23806) -> begin
(

let uu____23829 = (is_const_match tm1)
in (match (uu____23829) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| FStar_Pervasives_Native.None -> begin
tm1
end))
end
| uu____23838 -> begin
tm1
end))
end))))))))))))))
end))))
and rebuild : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____23848 -> ((

let uu____23850 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____23852 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____23854 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____23862 = (

let uu____23864 = (

let uu____23867 = (firstn (Prims.parse_int "4") stack)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____23867))
in (stack_to_string uu____23864))
in (FStar_Util.print4 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n" uu____23850 uu____23852 uu____23854 uu____23862)))));
(

let uu____23892 = (FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv (FStar_Options.Other ("NormRebuild")))
in (match (uu____23892) with
| true -> begin
(

let uu____23896 = (FStar_Syntax_Util.unbound_variables t)
in (match (uu____23896) with
| [] -> begin
()
end
| bvs -> begin
((

let uu____23903 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____23905 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____23907 = (

let uu____23909 = (FStar_All.pipe_right bvs (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right uu____23909 (FStar_String.concat ", ")))
in (FStar_Util.print3 "!!! Rebuild (%s) %s, free vars=%s\n" uu____23903 uu____23905 uu____23907))));
(failwith "DIE!");
)
end))
end
| uu____23926 -> begin
()
end));
)));
(

let f_opt = (is_fext_on_domain t)
in (

let uu____23931 = ((FStar_All.pipe_right f_opt FStar_Util.is_some) && (match (stack) with
| (Arg (uu____23939))::uu____23940 -> begin
true
end
| uu____23950 -> begin
false
end))
in (match (uu____23931) with
| true -> begin
(

let uu____23953 = (FStar_All.pipe_right f_opt FStar_Util.must)
in (FStar_All.pipe_right uu____23953 (norm cfg env stack)))
end
| uu____23956 -> begin
(

let t1 = (maybe_simplify cfg env stack t)
in (match (stack) with
| [] -> begin
t1
end
| (Debug (tm, time_then))::stack1 -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(

let time_now = (FStar_Util.now ())
in (

let uu____23967 = (

let uu____23969 = (

let uu____23971 = (FStar_Util.time_diff time_then time_now)
in (FStar_Pervasives_Native.snd uu____23971))
in (FStar_Util.string_of_int uu____23969))
in (

let uu____23978 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____23980 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized term (%s ms) %s\n\tto term %s\n" uu____23967 uu____23978 uu____23980)))))
end
| uu____23983 -> begin
()
end);
(rebuild cfg env stack1 t1);
)
end
| (Cfg (cfg1))::stack1 -> begin
(rebuild cfg1 env stack1 t1)
end
| (Meta (uu____23989, m, r))::stack1 -> begin
(

let t2 = (mk (FStar_Syntax_Syntax.Tm_meta (((t1), (m)))) r)
in (rebuild cfg env stack1 t2))
end
| (MemoLazy (r))::stack1 -> begin
((set_memo cfg r ((env), (t1)));
(FStar_TypeChecker_Cfg.log cfg (fun uu____24018 -> (

let uu____24019 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____24019))));
(rebuild cfg env stack1 t1);
)
end
| (Let (env', bs, lb, r))::stack1 -> begin
(

let body = (FStar_Syntax_Subst.close bs t1)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) FStar_Pervasives_Native.None r)
in (rebuild cfg env' stack1 t2)))
end
| (Abs (env', bs, env'', lopt, r))::stack1 -> begin
(

let bs1 = (norm_binders cfg env' bs)
in (

let lopt1 = (norm_lcomp_opt cfg env'' lopt)
in (

let uu____24062 = (

let uu___2785_24063 = (FStar_Syntax_Util.abs bs1 t1 lopt1)
in {FStar_Syntax_Syntax.n = uu___2785_24063.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___2785_24063.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack1 uu____24062))))
end
| (Arg (Univ (uu____24066), uu____24067, uu____24068))::uu____24069 -> begin
(failwith "Impossible")
end
| (Arg (Dummy, uu____24073, uu____24074))::uu____24075 -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack1 -> begin
(

let t2 = (FStar_Syntax_Syntax.mk_Tm_uinst t1 us)
in (rebuild cfg env stack1 t2))
end
| (Arg (Clos (env_arg, tm, uu____24091, uu____24092), aq, r))::stack1 when (

let uu____24144 = (head_of t1)
in (FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24144)) -> begin
(

let t2 = (

let uu____24148 = (

let uu____24153 = (

let uu____24154 = (closure_as_term cfg env_arg tm)
in ((uu____24154), (aq)))
in (FStar_Syntax_Syntax.extend_app t1 uu____24153))
in (uu____24148 FStar_Pervasives_Native.None r))
in (rebuild cfg env stack1 t2))
end
| (Arg (Clos (env_arg, tm, m, uu____24164), aq, r))::stack1 -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____24219 -> (

let uu____24220 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" uu____24220))));
(match ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.iota))) with
| true -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.hnf) with
| true -> begin
(

let arg = (closure_as_term cfg env_arg tm)
in (

let t2 = (FStar_Syntax_Syntax.extend_app t1 ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack1 t2)))
end
| uu____24233 -> begin
(

let stack2 = (App (((env), (t1), (aq), (r))))::stack1
in (norm cfg env_arg stack2 tm))
end)
end
| uu____24238 -> begin
(

let uu____24240 = (FStar_ST.op_Bang m)
in (match (uu____24240) with
| FStar_Pervasives_Native.None -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.hnf) with
| true -> begin
(

let arg = (closure_as_term cfg env_arg tm)
in (

let t2 = (FStar_Syntax_Syntax.extend_app t1 ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack1 t2)))
end
| uu____24323 -> begin
(

let stack2 = (MemoLazy (m))::(App (((env), (t1), (aq), (r))))::stack1
in (norm cfg env_arg stack2 tm))
end)
end
| FStar_Pervasives_Native.Some (uu____24328, a) -> begin
(

let t2 = (FStar_Syntax_Syntax.extend_app t1 ((a), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack1 t2))
end))
end);
)
end
| (App (env1, head1, aq, r))::stack' when (should_reify cfg stack) -> begin
(

let t0 = t1
in (

let fallback = (fun msg uu____24384 -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____24389 -> (

let uu____24390 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not reifying%s: %s\n" msg uu____24390))));
(

let t2 = (FStar_Syntax_Syntax.extend_app head1 ((t1), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack' t2));
))
in (

let uu____24400 = (

let uu____24401 = (FStar_Syntax_Subst.compress t1)
in uu____24401.FStar_Syntax_Syntax.n)
in (match (uu____24400) with
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic (m, ty)) -> begin
(do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty)
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, ty)) -> begin
(

let lifted = (

let uu____24429 = (closure_as_term cfg env1 ty)
in (reify_lift cfg t2 msrc mtgt uu____24429))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____24433 -> (

let uu____24434 = (FStar_Syntax_Print.term_to_string lifted)
in (FStar_Util.print1 "Reified lift to (1): %s\n" uu____24434))));
(

let uu____24437 = (FStar_List.tl stack)
in (norm cfg env1 uu____24437 lifted));
))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____24438)); FStar_Syntax_Syntax.pos = uu____24439; FStar_Syntax_Syntax.vars = uu____24440}, ((e, uu____24442))::[]) -> begin
(norm cfg env1 stack' e)
end
| FStar_Syntax_Syntax.Tm_app (uu____24481) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.primops -> begin
(

let uu____24498 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____24498) with
| (hd1, args) -> begin
(

let uu____24541 = (

let uu____24542 = (FStar_Syntax_Util.un_uinst hd1)
in uu____24542.FStar_Syntax_Syntax.n)
in (match (uu____24541) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____24546 = (FStar_TypeChecker_Cfg.find_prim_step cfg fv)
in (match (uu____24546) with
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Cfg.name = uu____24549; FStar_TypeChecker_Cfg.arity = uu____24550; FStar_TypeChecker_Cfg.univ_arity = uu____24551; FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.Some (n1); FStar_TypeChecker_Cfg.strong_reduction_ok = uu____24553; FStar_TypeChecker_Cfg.requires_binder_substitution = uu____24554; FStar_TypeChecker_Cfg.interpretation = uu____24555; FStar_TypeChecker_Cfg.interpretation_nbe = uu____24556}) when (Prims.op_Equality (FStar_List.length args) n1) -> begin
(norm cfg env1 stack' t1)
end
| uu____24592 -> begin
(fallback " (3)" ())
end))
end
| uu____24596 -> begin
(fallback " (4)" ())
end))
end))
end
| uu____24598 -> begin
(fallback " (2)" ())
end))))
end
| (App (env1, head1, aq, r))::stack1 -> begin
(

let t2 = (FStar_Syntax_Syntax.extend_app head1 ((t1), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack1 t2))
end
| (Match (env', branches, cfg1, r))::stack1 -> begin
((FStar_TypeChecker_Cfg.log cfg1 (fun uu____24624 -> (

let uu____24625 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" uu____24625))));
(

let scrutinee_env = env
in (

let env1 = env'
in (

let scrutinee = t1
in (

let norm_and_rebuild_match = (fun uu____24636 -> ((FStar_TypeChecker_Cfg.log cfg1 (fun uu____24641 -> (

let uu____24642 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____24644 = (

let uu____24646 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____24676 -> (match (uu____24676) with
| (p, uu____24687, uu____24688) -> begin
(FStar_Syntax_Print.pat_to_string p)
end))))
in (FStar_All.pipe_right uu____24646 (FStar_String.concat "\n\t")))
in (FStar_Util.print2 "match is irreducible: scrutinee=%s\nbranches=%s\n" uu____24642 uu____24644)))));
(

let whnf = (cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak || cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.hnf)
in (

let cfg_exclude_zeta = (

let new_delta = (FStar_All.pipe_right cfg1.FStar_TypeChecker_Cfg.delta_level (FStar_List.filter (fun uu___16_24710 -> (match (uu___16_24710) with
| FStar_TypeChecker_Env.InliningDelta -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| uu____24714 -> begin
false
end))))
in (

let steps = (

let uu___2953_24717 = cfg1.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___2953_24717.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___2953_24717.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = false; FStar_TypeChecker_Cfg.weak = uu___2953_24717.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___2953_24717.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___2953_24717.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___2953_24717.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_only = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_fully = uu___2953_24717.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_tac = false; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___2953_24717.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___2953_24717.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___2953_24717.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___2953_24717.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___2953_24717.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___2953_24717.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___2953_24717.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___2953_24717.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___2953_24717.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___2953_24717.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___2953_24717.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___2953_24717.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___2953_24717.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___2953_24717.FStar_TypeChecker_Cfg.for_extraction})
in (

let uu___2956_24724 = cfg1
in {FStar_TypeChecker_Cfg.steps = steps; FStar_TypeChecker_Cfg.tcenv = uu___2956_24724.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___2956_24724.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = new_delta; FStar_TypeChecker_Cfg.primitive_steps = uu___2956_24724.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___2956_24724.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___2956_24724.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___2956_24724.FStar_TypeChecker_Cfg.reifying})))
in (

let norm_or_whnf = (fun env2 t2 -> (match (whnf) with
| true -> begin
(closure_as_term cfg_exclude_zeta env2 t2)
end
| uu____24738 -> begin
(norm cfg_exclude_zeta env2 [] t2)
end))
in (

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____24799) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____24830 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____24919 uu____24920 -> (match (((uu____24919), (uu____24920))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____25070 = (norm_pat env3 p1)
in (match (uu____25070) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____24830) with
| (pats1, env3) -> begin
(((

let uu___2984_25240 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___2984_25240.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___2988_25261 = x
in (

let uu____25262 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___2988_25261.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2988_25261.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____25262}))
in (((

let uu___2991_25276 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___2991_25276.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___2995_25287 = x
in (

let uu____25288 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___2995_25287.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2995_25287.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____25288}))
in (((

let uu___2998_25302 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___2998_25302.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t2) -> begin
(

let x1 = (

let uu___3004_25318 = x
in (

let uu____25319 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___3004_25318.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___3004_25318.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____25319}))
in (

let t3 = (norm_or_whnf env2 t2)
in (((

let uu___3008_25334 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t3))); FStar_Syntax_Syntax.p = uu___3008_25334.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let branches1 = (match (env1) with
| [] when whnf -> begin
branches
end
| uu____25378 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch1 -> (

let uu____25408 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____25408) with
| (p, wopt, e) -> begin
(

let uu____25428 = (norm_pat env1 p)
in (match (uu____25428) with
| (p1, env2) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____25483 = (norm_or_whnf env2 w)
in FStar_Pervasives_Native.Some (uu____25483))
end)
in (

let e1 = (norm_or_whnf env2 e)
in (FStar_Syntax_Util.branch ((p1), (wopt1), (e1)))))
end))
end)))))
end)
in (

let scrutinee1 = (

let uu____25500 = ((((cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.iota && (not (cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak))) && (not (cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars))) && cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee) && (maybe_weakly_reduced scrutinee))
in (match (uu____25500) with
| true -> begin
(norm (

let uu___3027_25507 = cfg1
in {FStar_TypeChecker_Cfg.steps = (

let uu___3029_25510 = cfg1.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___3029_25510.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___3029_25510.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___3029_25510.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___3029_25510.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___3029_25510.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___3029_25510.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___3029_25510.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___3029_25510.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___3029_25510.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___3029_25510.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___3029_25510.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___3029_25510.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___3029_25510.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___3029_25510.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___3029_25510.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___3029_25510.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___3029_25510.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___3029_25510.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___3029_25510.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___3029_25510.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___3029_25510.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___3029_25510.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___3029_25510.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = false; FStar_TypeChecker_Cfg.nbe_step = uu___3029_25510.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___3029_25510.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___3027_25507.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___3027_25507.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___3027_25507.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___3027_25507.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___3027_25507.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___3027_25507.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___3027_25507.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___3027_25507.FStar_TypeChecker_Cfg.reifying}) scrutinee_env [] scrutinee)
end
| uu____25512 -> begin
scrutinee
end))
in (

let uu____25514 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee1), (branches1)))) r)
in (rebuild cfg1 env1 stack1 uu____25514))))))));
))
in (

let rec is_cons = (fun head1 -> (

let uu____25540 = (

let uu____25541 = (FStar_Syntax_Subst.compress head1)
in uu____25541.FStar_Syntax_Syntax.n)
in (match (uu____25540) with
| FStar_Syntax_Syntax.Tm_uinst (h, uu____25546) -> begin
(is_cons h)
end
| FStar_Syntax_Syntax.Tm_constant (uu____25551) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____25553; FStar_Syntax_Syntax.fv_delta = uu____25554; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____25556; FStar_Syntax_Syntax.fv_delta = uu____25557; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____25558))}) -> begin
true
end
| uu____25566 -> begin
false
end)))
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

let scrutinee2 = (FStar_Syntax_Util.unlazy scrutinee1)
in (

let uu____25735 = (FStar_Syntax_Util.head_and_args scrutinee2)
in (match (uu____25735) with
| (head1, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____25832) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (FStar_Const.eq_const s s') -> begin
FStar_Util.Inl ([])
end
| uu____25874 -> begin
(

let uu____25875 = (

let uu____25877 = (is_cons head1)
in (not (uu____25877)))
in FStar_Util.Inr (uu____25875))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let uu____25906 = (

let uu____25907 = (FStar_Syntax_Util.un_uinst head1)
in uu____25907.FStar_Syntax_Syntax.n)
in (match (uu____25906) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| uu____25926 -> begin
(

let uu____25927 = (

let uu____25929 = (is_cons head1)
in (not (uu____25929)))
in FStar_Util.Inr (uu____25927))
end))
end)
end)))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t2, uu____26020))::rest_a, ((p1, uu____26023))::rest_p) -> begin
(

let uu____26082 = (matches_pat t2 p1)
in (match (uu____26082) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____26135 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee1 p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p1, wopt, b))::rest -> begin
(

let uu____26258 = (matches_pat scrutinee1 p1)
in (match (uu____26258) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee1 rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
((FStar_TypeChecker_Cfg.log cfg1 (fun uu____26304 -> (

let uu____26305 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____26307 = (

let uu____26309 = (FStar_List.map (fun uu____26321 -> (match (uu____26321) with
| (uu____26327, t2) -> begin
(FStar_Syntax_Print.term_to_string t2)
end)) s)
in (FStar_All.pipe_right uu____26309 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" uu____26305 uu____26307)))));
(

let env0 = env1
in (

let env2 = (FStar_List.fold_left (fun env2 uu____26363 -> (match (uu____26363) with
| (bv, t2) -> begin
(

let uu____26386 = (

let uu____26393 = (

let uu____26396 = (FStar_Syntax_Syntax.mk_binder bv)
in FStar_Pervasives_Native.Some (uu____26396))
in (

let uu____26397 = (

let uu____26398 = (

let uu____26430 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ((([]), (t2)))))
in (([]), (t2), (uu____26430), (false)))
in Clos (uu____26398))
in ((uu____26393), (uu____26397))))
in (uu____26386)::env2)
end)) env1 s)
in (

let uu____26523 = (guard_when_clause wopt b rest)
in (norm cfg1 env2 stack1 uu____26523))));
)
end))
end))
in (match (cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.iota) with
| true -> begin
(matches scrutinee branches)
end
| uu____26525 -> begin
(norm_and_rebuild_match ())
end)))))))));
)
end))
end)));
))


let normalize_with_primitive_steps : FStar_TypeChecker_Cfg.primitive_step Prims.list  ->  FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun ps s e t -> (

let c = (FStar_TypeChecker_Cfg.config' ps s e)
in ((FStar_TypeChecker_Cfg.log_cfg c (fun uu____26556 -> (

let uu____26557 = (FStar_TypeChecker_Cfg.cfg_to_string c)
in (FStar_Util.print1 "Cfg = %s\n" uu____26557))));
(

let uu____26560 = (is_nbe_request s)
in (match (uu____26560) with
| true -> begin
((FStar_TypeChecker_Cfg.log_top c (fun uu____26566 -> (

let uu____26567 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Starting NBE for (%s) {\n" uu____26567))));
(FStar_TypeChecker_Cfg.log_top c (fun uu____26573 -> (

let uu____26574 = (FStar_TypeChecker_Cfg.cfg_to_string c)
in (FStar_Util.print1 ">>> cfg = %s\n" uu____26574))));
(

let uu____26577 = (FStar_Util.record_time (fun uu____26584 -> (nbe_eval c s t)))
in (match (uu____26577) with
| (r, ms) -> begin
((FStar_TypeChecker_Cfg.log_top c (fun uu____26593 -> (

let uu____26594 = (FStar_Syntax_Print.term_to_string r)
in (

let uu____26596 = (FStar_Util.string_of_int ms)
in (FStar_Util.print2 "}\nNormalization result = (%s) in %s ms\n" uu____26594 uu____26596)))));
r;
)
end));
)
end
| uu____26599 -> begin
((FStar_TypeChecker_Cfg.log_top c (fun uu____26604 -> (

let uu____26605 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Starting normalizer for (%s) {\n" uu____26605))));
(FStar_TypeChecker_Cfg.log_top c (fun uu____26611 -> (

let uu____26612 = (FStar_TypeChecker_Cfg.cfg_to_string c)
in (FStar_Util.print1 ">>> cfg = %s\n" uu____26612))));
(

let uu____26615 = (FStar_Util.record_time (fun uu____26622 -> (norm c [] [] t)))
in (match (uu____26615) with
| (r, ms) -> begin
((FStar_TypeChecker_Cfg.log_top c (fun uu____26637 -> (

let uu____26638 = (FStar_Syntax_Print.term_to_string r)
in (

let uu____26640 = (FStar_Util.string_of_int ms)
in (FStar_Util.print2 "}\nNormalization result = (%s) in %s ms\n" uu____26638 uu____26640)))));
r;
)
end));
)
end));
)))


let normalize : FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (

let uu____26659 = (

let uu____26663 = (

let uu____26665 = (FStar_TypeChecker_Env.current_module e)
in (FStar_Ident.string_of_lid uu____26665))
in FStar_Pervasives_Native.Some (uu____26663))
in (FStar_Profiling.profile (fun uu____26668 -> (normalize_with_primitive_steps [] s e t)) uu____26659 "FStar.TypeChecker.Normalize")))


let normalize_comp : FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e c -> (

let cfg = (FStar_TypeChecker_Cfg.config s e)
in ((FStar_TypeChecker_Cfg.log_top cfg (fun uu____26690 -> (

let uu____26691 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Starting normalizer for computation (%s) {\n" uu____26691))));
(FStar_TypeChecker_Cfg.log_top cfg (fun uu____26697 -> (

let uu____26698 = (FStar_TypeChecker_Cfg.cfg_to_string cfg)
in (FStar_Util.print1 ">>> cfg = %s\n" uu____26698))));
(

let uu____26701 = (FStar_Util.record_time (fun uu____26708 -> (norm_comp cfg [] c)))
in (match (uu____26701) with
| (c1, ms) -> begin
((FStar_TypeChecker_Cfg.log_top cfg (fun uu____26723 -> (

let uu____26724 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____26726 = (FStar_Util.string_of_int ms)
in (FStar_Util.print2 "}\nNormalization result = (%s) in %s ms\n" uu____26724 uu____26726)))));
c1;
)
end));
)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let uu____26740 = (FStar_TypeChecker_Cfg.config [] env)
in (norm_universe uu____26740 [] u)))


let non_info_norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let steps = (FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.Unascribe)::(FStar_TypeChecker_Env.ForExtraction)::[]
in (

let uu____26762 = (normalize steps env t)
in (FStar_TypeChecker_Env.non_informative env uu____26762))))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____26774) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info_norm env t) -> begin
(

let uu___3197_26793 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.pos = uu___3197_26793.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___3197_26793.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name env ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____26800 = ((FStar_Syntax_Util.is_ghost_effect l) && (non_info_norm env ct.FStar_Syntax_Syntax.result_typ))
in (match (uu____26800) with
| true -> begin
(

let ct1 = (

let uu____26804 = (downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)
in (match (uu____26804) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let flags = (

let uu____26811 = (FStar_Ident.lid_equals pure_eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____26811) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::ct.FStar_Syntax_Syntax.flags
end
| uu____26816 -> begin
ct.FStar_Syntax_Syntax.flags
end))
in (

let uu___3207_26818 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___3207_26818.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = uu___3207_26818.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___3207_26818.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags}))
end
| FStar_Pervasives_Native.None -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu___3211_26820 = ct1
in {FStar_Syntax_Syntax.comp_univs = uu___3211_26820.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu___3211_26820.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___3211_26820.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___3211_26820.FStar_Syntax_Syntax.flags}))
end))
in (

let uu___3214_26821 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___3214_26821.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___3214_26821.FStar_Syntax_Syntax.vars}))
end
| uu____26822 -> begin
c
end)))
end
| uu____26824 -> begin
c
end))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_TypeChecker_Common.lcomp = (fun env lc -> (

let uu____26836 = ((FStar_Syntax_Util.is_ghost_effect lc.FStar_TypeChecker_Common.eff_name) && (non_info_norm env lc.FStar_TypeChecker_Common.res_typ))
in (match (uu____26836) with
| true -> begin
(

let uu____26839 = (downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name)
in (match (uu____26839) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let uu___3222_26843 = (FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env) (fun g -> g) lc)
in {FStar_TypeChecker_Common.eff_name = pure_eff; FStar_TypeChecker_Common.res_typ = uu___3222_26843.FStar_TypeChecker_Common.res_typ; FStar_TypeChecker_Common.cflags = uu___3222_26843.FStar_TypeChecker_Common.cflags; FStar_TypeChecker_Common.comp_thunk = uu___3222_26843.FStar_TypeChecker_Common.comp_thunk})
end
| FStar_Pervasives_Native.None -> begin
lc
end))
end
| uu____26846 -> begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (

let t1 = (FStar_All.try_with (fun uu___3229_26862 -> (match (()) with
| () -> begin
(normalize ((FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env t)
end)) (fun uu___3228_26865 -> ((

let uu____26867 = (

let uu____26873 = (

let uu____26875 = (FStar_Util.message_of_exn uu___3228_26865)
in (FStar_Util.format1 "Normalization failed with error %s\n" uu____26875))
in ((FStar_Errors.Warning_NormalizationFailure), (uu____26873)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____26867));
t;
)))
in (FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let c1 = (FStar_All.try_with (fun uu___3239_26894 -> (match (()) with
| () -> begin
(

let uu____26895 = (FStar_TypeChecker_Cfg.config ((FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env)
in (norm_comp uu____26895 [] c))
end)) (fun uu___3238_26904 -> ((

let uu____26906 = (

let uu____26912 = (

let uu____26914 = (FStar_Util.message_of_exn uu___3238_26904)
in (FStar_Util.format1 "Normalization failed with error %s\n" uu____26914))
in ((FStar_Errors.Warning_NormalizationFailure), (uu____26912)))
in (FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____26906));
c;
)))
in (FStar_Syntax_Print.comp_to_string' env.FStar_TypeChecker_Env.dsenv c1)))


let normalize_refinement : FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (

let t = (normalize (FStar_List.append steps ((FStar_TypeChecker_Env.Beta)::[])) env t0)
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

let uu____26963 = (

let uu____26964 = (

let uu____26971 = (FStar_Syntax_Util.mk_conj_simp phi1 phi)
in ((y), (uu____26971)))
in FStar_Syntax_Syntax.Tm_refine (uu____26964))
in (mk uu____26963 t01.FStar_Syntax_Syntax.pos))
end
| uu____26976 -> begin
t2
end))
end
| uu____26977 -> begin
t2
end)))
in (aux t))))


let whnf_steps : FStar_TypeChecker_Env.step Prims.list = (FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Beta)::[]


let unfold_whnf' : FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun steps env t -> (normalize (FStar_List.append steps whnf_steps) env t))


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (unfold_whnf' [] env t))


let reduce_or_remove_uvar_solutions : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun remove env t -> (normalize (FStar_List.append (match (remove) with
| true -> begin
(FStar_TypeChecker_Env.CheckNoUvars)::[]
end
| uu____27029 -> begin
[]
end) ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.CompressUvars)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota))::(FStar_TypeChecker_Env.NoFullNorm)::[])) env t))


let reduce_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions false env t))


let remove_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions true env t))


let eta_expand_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e t_e -> (

let uu____27071 = (FStar_Syntax_Util.arrow_formals_comp t_e)
in (match (uu____27071) with
| (formals, c) -> begin
(match (formals) with
| [] -> begin
e
end
| uu____27108 -> begin
(

let uu____27117 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____27117) with
| (actuals, uu____27127, uu____27128) -> begin
(match ((Prims.op_Equality (FStar_List.length actuals) (FStar_List.length formals))) with
| true -> begin
e
end
| uu____27146 -> begin
(

let uu____27148 = (FStar_All.pipe_right formals FStar_Syntax_Util.args_of_binders)
in (match (uu____27148) with
| (binders, args) -> begin
(

let uu____27159 = (FStar_Syntax_Syntax.mk_Tm_app e args FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Util.abs binders uu____27159 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c)))))
end))
end)
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(eta_expand_with_type env t x.FStar_Syntax_Syntax.sort)
end
| uu____27174 -> begin
(

let uu____27175 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____27175) with
| (head1, args) -> begin
(

let uu____27218 = (

let uu____27219 = (FStar_Syntax_Subst.compress head1)
in uu____27219.FStar_Syntax_Syntax.n)
in (match (uu____27218) with
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____27240 = (

let uu____27255 = (FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Syntax_Util.arrow_formals uu____27255))
in (match (uu____27240) with
| (formals, _tres) -> begin
(match ((Prims.op_Equality (FStar_List.length formals) (FStar_List.length args))) with
| true -> begin
t
end
| uu____27293 -> begin
(

let uu____27295 = (env.FStar_TypeChecker_Env.type_of (

let uu___3309_27303 = env
in {FStar_TypeChecker_Env.solver = uu___3309_27303.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___3309_27303.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___3309_27303.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___3309_27303.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___3309_27303.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___3309_27303.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___3309_27303.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___3309_27303.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___3309_27303.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___3309_27303.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___3309_27303.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___3309_27303.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___3309_27303.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___3309_27303.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___3309_27303.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___3309_27303.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___3309_27303.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___3309_27303.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___3309_27303.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___3309_27303.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___3309_27303.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___3309_27303.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___3309_27303.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___3309_27303.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___3309_27303.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___3309_27303.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___3309_27303.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___3309_27303.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___3309_27303.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___3309_27303.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___3309_27303.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___3309_27303.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___3309_27303.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___3309_27303.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___3309_27303.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___3309_27303.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___3309_27303.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___3309_27303.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___3309_27303.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___3309_27303.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___3309_27303.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___3309_27303.FStar_TypeChecker_Env.erasable_types_tab}) t)
in (match (uu____27295) with
| (uu____27306, ty, uu____27308) -> begin
(eta_expand_with_type env t ty)
end))
end)
end))
end
| uu____27309 -> begin
(

let uu____27310 = (env.FStar_TypeChecker_Env.type_of (

let uu___3316_27318 = env
in {FStar_TypeChecker_Env.solver = uu___3316_27318.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___3316_27318.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___3316_27318.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___3316_27318.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___3316_27318.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___3316_27318.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___3316_27318.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___3316_27318.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___3316_27318.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___3316_27318.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___3316_27318.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___3316_27318.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___3316_27318.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___3316_27318.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___3316_27318.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___3316_27318.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___3316_27318.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___3316_27318.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___3316_27318.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___3316_27318.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___3316_27318.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___3316_27318.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___3316_27318.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___3316_27318.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___3316_27318.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___3316_27318.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___3316_27318.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___3316_27318.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___3316_27318.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___3316_27318.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___3316_27318.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___3316_27318.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___3316_27318.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___3316_27318.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___3316_27318.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___3316_27318.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___3316_27318.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___3316_27318.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___3316_27318.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___3316_27318.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___3316_27318.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___3316_27318.FStar_TypeChecker_Env.erasable_types_tab}) t)
in (match (uu____27310) with
| (uu____27321, ty, uu____27323) -> begin
(eta_expand_with_type env t ty)
end))
end))
end))
end))


let rec elim_delayed_subst_term : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let elim_bv = (fun x -> (

let uu___3328_27405 = x
in (

let uu____27406 = (elim_delayed_subst_term x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___3328_27405.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___3328_27405.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____27406})))
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____27409) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_bvar (uu____27433) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_name (uu____27434) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_fvar (uu____27435) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uinst (uu____27436) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_constant (uu____27443) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (uu____27444) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_lazy (uu____27445) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t1
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, rc_opt) -> begin
(

let elim_rc = (fun rc -> (

let uu___3354_27479 = rc
in (

let uu____27480 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ elim_delayed_subst_term)
in (

let uu____27489 = (elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags)
in {FStar_Syntax_Syntax.residual_effect = uu___3354_27479.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____27480; FStar_Syntax_Syntax.residual_flags = uu____27489}))))
in (

let uu____27492 = (

let uu____27493 = (

let uu____27512 = (elim_delayed_subst_binders bs)
in (

let uu____27521 = (elim_delayed_subst_term t2)
in (

let uu____27524 = (FStar_Util.map_opt rc_opt elim_rc)
in ((uu____27512), (uu____27521), (uu____27524)))))
in FStar_Syntax_Syntax.Tm_abs (uu____27493))
in (mk1 uu____27492)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____27561 = (

let uu____27562 = (

let uu____27577 = (elim_delayed_subst_binders bs)
in (

let uu____27586 = (elim_delayed_subst_comp c)
in ((uu____27577), (uu____27586))))
in FStar_Syntax_Syntax.Tm_arrow (uu____27562))
in (mk1 uu____27561))
end
| FStar_Syntax_Syntax.Tm_refine (bv, phi) -> begin
(

let uu____27605 = (

let uu____27606 = (

let uu____27613 = (elim_bv bv)
in (

let uu____27614 = (elim_delayed_subst_term phi)
in ((uu____27613), (uu____27614))))
in FStar_Syntax_Syntax.Tm_refine (uu____27606))
in (mk1 uu____27605))
end
| FStar_Syntax_Syntax.Tm_app (t2, args) -> begin
(

let uu____27645 = (

let uu____27646 = (

let uu____27663 = (elim_delayed_subst_term t2)
in (

let uu____27666 = (elim_delayed_subst_args args)
in ((uu____27663), (uu____27666))))
in FStar_Syntax_Syntax.Tm_app (uu____27646))
in (mk1 uu____27645))
end
| FStar_Syntax_Syntax.Tm_match (t2, branches) -> begin
(

let rec elim_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu___3376_27738 = p
in (

let uu____27739 = (

let uu____27740 = (elim_bv x)
in FStar_Syntax_Syntax.Pat_var (uu____27740))
in {FStar_Syntax_Syntax.v = uu____27739; FStar_Syntax_Syntax.p = uu___3376_27738.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu___3380_27742 = p
in (

let uu____27743 = (

let uu____27744 = (elim_bv x)
in FStar_Syntax_Syntax.Pat_wild (uu____27744))
in {FStar_Syntax_Syntax.v = uu____27743; FStar_Syntax_Syntax.p = uu___3380_27742.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let uu___3386_27751 = p
in (

let uu____27752 = (

let uu____27753 = (

let uu____27760 = (elim_bv x)
in (

let uu____27761 = (elim_delayed_subst_term t0)
in ((uu____27760), (uu____27761))))
in FStar_Syntax_Syntax.Pat_dot_term (uu____27753))
in {FStar_Syntax_Syntax.v = uu____27752; FStar_Syntax_Syntax.p = uu___3386_27751.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu___3392_27786 = p
in (

let uu____27787 = (

let uu____27788 = (

let uu____27802 = (FStar_List.map (fun uu____27828 -> (match (uu____27828) with
| (x, b) -> begin
(

let uu____27845 = (elim_pat x)
in ((uu____27845), (b)))
end)) pats)
in ((fv), (uu____27802)))
in FStar_Syntax_Syntax.Pat_cons (uu____27788))
in {FStar_Syntax_Syntax.v = uu____27787; FStar_Syntax_Syntax.p = uu___3392_27786.FStar_Syntax_Syntax.p}))
end
| uu____27860 -> begin
p
end))
in (

let elim_branch = (fun uu____27884 -> (match (uu____27884) with
| (pat, wopt, t3) -> begin
(

let uu____27910 = (elim_pat pat)
in (

let uu____27913 = (FStar_Util.map_opt wopt elim_delayed_subst_term)
in (

let uu____27916 = (elim_delayed_subst_term t3)
in ((uu____27910), (uu____27913), (uu____27916)))))
end))
in (

let uu____27921 = (

let uu____27922 = (

let uu____27945 = (elim_delayed_subst_term t2)
in (

let uu____27948 = (FStar_List.map elim_branch branches)
in ((uu____27945), (uu____27948))))
in FStar_Syntax_Syntax.Tm_match (uu____27922))
in (mk1 uu____27921))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, a, lopt) -> begin
(

let elim_ascription = (fun uu____28079 -> (match (uu____28079) with
| (tc, topt) -> begin
(

let uu____28114 = (match (tc) with
| FStar_Util.Inl (t3) -> begin
(

let uu____28124 = (elim_delayed_subst_term t3)
in FStar_Util.Inl (uu____28124))
end
| FStar_Util.Inr (c) -> begin
(

let uu____28126 = (elim_delayed_subst_comp c)
in FStar_Util.Inr (uu____28126))
end)
in (

let uu____28127 = (FStar_Util.map_opt topt elim_delayed_subst_term)
in ((uu____28114), (uu____28127))))
end))
in (

let uu____28136 = (

let uu____28137 = (

let uu____28164 = (elim_delayed_subst_term t2)
in (

let uu____28167 = (elim_ascription a)
in ((uu____28164), (uu____28167), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____28137))
in (mk1 uu____28136)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t2) -> begin
(

let elim_lb = (fun lb -> (

let uu___3422_28230 = lb
in (

let uu____28231 = (elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____28234 = (elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___3422_28230.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___3422_28230.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____28231; FStar_Syntax_Syntax.lbeff = uu___3422_28230.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____28234; FStar_Syntax_Syntax.lbattrs = uu___3422_28230.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___3422_28230.FStar_Syntax_Syntax.lbpos}))))
in (

let uu____28237 = (

let uu____28238 = (

let uu____28252 = (

let uu____28260 = (FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs))
in (((FStar_Pervasives_Native.fst lbs)), (uu____28260)))
in (

let uu____28272 = (elim_delayed_subst_term t2)
in ((uu____28252), (uu____28272))))
in FStar_Syntax_Syntax.Tm_let (uu____28238))
in (mk1 uu____28237)))
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uvar (((u), (s)))))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi)
in (

let uu____28317 = (

let uu____28318 = (

let uu____28325 = (elim_delayed_subst_term tm)
in ((uu____28325), (qi1)))
in FStar_Syntax_Syntax.Tm_quoted (uu____28318))
in (mk1 uu____28317)))
end
| FStar_Syntax_Syntax.Tm_meta (t2, md) -> begin
(

let uu____28336 = (

let uu____28337 = (

let uu____28344 = (elim_delayed_subst_term t2)
in (

let uu____28347 = (elim_delayed_subst_meta md)
in ((uu____28344), (uu____28347))))
in FStar_Syntax_Syntax.Tm_meta (uu____28337))
in (mk1 uu____28336))
end)))))
and elim_delayed_subst_cflags : FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun flags -> (FStar_List.map (fun uu___17_28356 -> (match (uu___17_28356) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____28360 = (elim_delayed_subst_term t)
in FStar_Syntax_Syntax.DECREASES (uu____28360))
end
| f -> begin
f
end)) flags))
and elim_delayed_subst_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun c -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____28383 = (

let uu____28384 = (

let uu____28393 = (elim_delayed_subst_term t)
in ((uu____28393), (uopt)))
in FStar_Syntax_Syntax.Total (uu____28384))
in (mk1 uu____28383))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____28410 = (

let uu____28411 = (

let uu____28420 = (elim_delayed_subst_term t)
in ((uu____28420), (uopt)))
in FStar_Syntax_Syntax.GTotal (uu____28411))
in (mk1 uu____28410))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___3455_28429 = ct
in (

let uu____28430 = (elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____28433 = (elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args)
in (

let uu____28444 = (elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu___3455_28429.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___3455_28429.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____28430; FStar_Syntax_Syntax.effect_args = uu____28433; FStar_Syntax_Syntax.flags = uu____28444}))))
in (mk1 (FStar_Syntax_Syntax.Comp (ct1))))
end)))
and elim_delayed_subst_meta : FStar_Syntax_Syntax.metadata  ->  FStar_Syntax_Syntax.metadata = (fun uu___18_28447 -> (match (uu___18_28447) with
| FStar_Syntax_Syntax.Meta_pattern (names1, args) -> begin
(

let uu____28482 = (

let uu____28503 = (FStar_List.map elim_delayed_subst_term names1)
in (

let uu____28512 = (FStar_List.map elim_delayed_subst_args args)
in ((uu____28503), (uu____28512))))
in FStar_Syntax_Syntax.Meta_pattern (uu____28482))
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let uu____28567 = (

let uu____28574 = (elim_delayed_subst_term t)
in ((m), (uu____28574)))
in FStar_Syntax_Syntax.Meta_monadic (uu____28567))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t) -> begin
(

let uu____28586 = (

let uu____28595 = (elim_delayed_subst_term t)
in ((m1), (m2), (uu____28595)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____28586))
end
| m -> begin
m
end))
and elim_delayed_subst_args : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun args -> (FStar_List.map (fun uu____28628 -> (match (uu____28628) with
| (t, q) -> begin
(

let uu____28647 = (elim_delayed_subst_term t)
in ((uu____28647), (q)))
end)) args))
and elim_delayed_subst_binders : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun bs -> (FStar_List.map (fun uu____28675 -> (match (uu____28675) with
| (x, q) -> begin
(

let uu____28694 = (

let uu___3481_28695 = x
in (

let uu____28696 = (elim_delayed_subst_term x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___3481_28695.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___3481_28695.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____28696}))
in ((uu____28694), (q)))
end)) bs))


let elim_uvars_aux_tc : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.comp) FStar_Util.either  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either) = (fun env univ_names binders tc -> (

let t = (match (((binders), (tc))) with
| ([], FStar_Util.Inl (t)) -> begin
t
end
| ([], FStar_Util.Inr (c)) -> begin
(failwith "Impossible: empty bindes with a comp")
end
| (uu____28804, FStar_Util.Inr (c)) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
end
| (uu____28836, FStar_Util.Inl (t)) -> begin
(

let uu____28858 = (

let uu____28865 = (

let uu____28866 = (

let uu____28881 = (FStar_Syntax_Syntax.mk_Total t)
in ((binders), (uu____28881)))
in FStar_Syntax_Syntax.Tm_arrow (uu____28866))
in (FStar_Syntax_Syntax.mk uu____28865))
in (uu____28858 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end)
in (

let uu____28894 = (FStar_Syntax_Subst.open_univ_vars univ_names t)
in (match (uu____28894) with
| (univ_names1, t1) -> begin
(

let t2 = (remove_uvar_solutions env t1)
in (

let t3 = (FStar_Syntax_Subst.close_univ_vars univ_names1 t2)
in (

let t4 = (elim_delayed_subst_term t3)
in (

let uu____28926 = (match (binders) with
| [] -> begin
(([]), (FStar_Util.Inl (t4)))
end
| uu____28999 -> begin
(

let uu____29000 = (

let uu____29009 = (

let uu____29010 = (FStar_Syntax_Subst.compress t4)
in uu____29010.FStar_Syntax_Syntax.n)
in ((uu____29009), (tc)))
in (match (uu____29000) with
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inr (uu____29039)) -> begin
((binders1), (FStar_Util.Inr (c)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inl (uu____29086)) -> begin
((binders1), (FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))))
end
| (uu____29131, FStar_Util.Inl (uu____29132)) -> begin
(([]), (FStar_Util.Inl (t4)))
end
| uu____29163 -> begin
(failwith "Impossible")
end))
end)
in (match (uu____28926) with
| (binders1, tc1) -> begin
((univ_names1), (binders1), (tc1))
end)))))
end))))


let elim_uvars_aux_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun env univ_names binders t -> (

let uu____29302 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl (t)))
in (match (uu____29302) with
| (univ_names1, binders1, tc) -> begin
(

let uu____29376 = (FStar_Util.left tc)
in ((univ_names1), (binders1), (uu____29376)))
end)))


let elim_uvars_aux_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) = (fun env univ_names binders c -> (

let uu____29430 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr (c)))
in (match (uu____29430) with
| (univ_names1, binders1, tc) -> begin
(

let uu____29504 = (FStar_Util.right tc)
in ((univ_names1), (binders1), (uu____29504)))
end)))


let rec elim_uvars : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, lids, lids') -> begin
(

let uu____29546 = (elim_uvars_aux_t env univ_names binders typ)
in (match (uu____29546) with
| (univ_names1, binders1, typ1) -> begin
(

let uu___3564_29586 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univ_names1), (binders1), (typ1), (lids), (lids'))); FStar_Syntax_Syntax.sigrng = uu___3564_29586.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3564_29586.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3564_29586.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3564_29586.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___3564_29586.FStar_Syntax_Syntax.sigopts})
end))
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uu___3570_29601 = s
in (

let uu____29602 = (

let uu____29603 = (

let uu____29612 = (FStar_List.map (elim_uvars env) sigs)
in ((uu____29612), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____29603))
in {FStar_Syntax_Syntax.sigel = uu____29602; FStar_Syntax_Syntax.sigrng = uu___3570_29601.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3570_29601.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3570_29601.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3570_29601.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___3570_29601.FStar_Syntax_Syntax.sigopts}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univ_names, typ, lident, i, lids) -> begin
(

let uu____29631 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____29631) with
| (univ_names1, uu____29655, typ1) -> begin
(

let uu___3584_29677 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univ_names1), (typ1), (lident), (i), (lids))); FStar_Syntax_Syntax.sigrng = uu___3584_29677.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3584_29677.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3584_29677.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3584_29677.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___3584_29677.FStar_Syntax_Syntax.sigopts})
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) -> begin
(

let uu____29684 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____29684) with
| (univ_names1, uu____29708, typ1) -> begin
(

let uu___3595_29730 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (univ_names1), (typ1))); FStar_Syntax_Syntax.sigrng = uu___3595_29730.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3595_29730.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3595_29730.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3595_29730.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___3595_29730.FStar_Syntax_Syntax.sigopts})
end))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____29760 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____29760) with
| (opening, lbunivs) -> begin
(

let elim = (fun t -> (

let uu____29785 = (

let uu____29786 = (

let uu____29787 = (FStar_Syntax_Subst.subst opening t)
in (remove_uvar_solutions env uu____29787))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____29786))
in (elim_delayed_subst_term uu____29785)))
in (

let lbtyp = (elim lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (elim lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___3611_29790 = lb
in {FStar_Syntax_Syntax.lbname = uu___3611_29790.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___3611_29790.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___3611_29790.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___3611_29790.FStar_Syntax_Syntax.lbpos}))))
end)))))
in (

let uu___3614_29791 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((b), (lbs1))), (lids))); FStar_Syntax_Syntax.sigrng = uu___3614_29791.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3614_29791.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3614_29791.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3614_29791.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___3614_29791.FStar_Syntax_Syntax.sigopts}))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(

let uu___3618_29798 = s
in (

let uu____29799 = (

let uu____29800 = (remove_uvar_solutions env t)
in FStar_Syntax_Syntax.Sig_main (uu____29800))
in {FStar_Syntax_Syntax.sigel = uu____29799; FStar_Syntax_Syntax.sigrng = uu___3618_29798.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3618_29798.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3618_29798.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3618_29798.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___3618_29798.FStar_Syntax_Syntax.sigopts}))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, t) -> begin
(

let uu____29804 = (elim_uvars_aux_t env us [] t)
in (match (uu____29804) with
| (us1, uu____29828, t1) -> begin
(

let uu___3629_29850 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((l), (us1), (t1))); FStar_Syntax_Syntax.sigrng = uu___3629_29850.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3629_29850.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3629_29850.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3629_29850.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___3629_29850.FStar_Syntax_Syntax.sigopts})
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____29852 = (elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit)
in (match (uu____29852) with
| (univs1, binders, uu____29871) -> begin
(

let uu____29892 = (

let uu____29897 = (FStar_Syntax_Subst.univ_var_opening univs1)
in (match (uu____29897) with
| (univs_opening, univs2) -> begin
(

let uu____29920 = (FStar_Syntax_Subst.univ_var_closing univs2)
in ((univs_opening), (uu____29920)))
end))
in (match (uu____29892) with
| (univs_opening, univs_closing) -> begin
(

let uu____29923 = (

let binders1 = (FStar_Syntax_Subst.open_binders binders)
in (

let uu____29929 = (FStar_Syntax_Subst.opening_of_binders binders1)
in (

let uu____29930 = (FStar_Syntax_Subst.closing_of_binders binders1)
in ((uu____29929), (uu____29930)))))
in (match (uu____29923) with
| (b_opening, b_closing) -> begin
(

let n1 = (FStar_List.length univs1)
in (

let n_binders = (FStar_List.length binders)
in (

let elim_tscheme = (fun uu____29956 -> (match (uu____29956) with
| (us, t) -> begin
(

let n_us = (FStar_List.length us)
in (

let uu____29974 = (FStar_Syntax_Subst.open_univ_vars us t)
in (match (uu____29974) with
| (us1, t1) -> begin
(

let uu____29985 = (

let uu____29994 = (FStar_All.pipe_right b_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____29999 = (FStar_All.pipe_right b_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____29994), (uu____29999))))
in (match (uu____29985) with
| (b_opening1, b_closing1) -> begin
(

let uu____30022 = (

let uu____30031 = (FStar_All.pipe_right univs_opening (FStar_Syntax_Subst.shift_subst (n_us + n_binders)))
in (

let uu____30036 = (FStar_All.pipe_right univs_closing (FStar_Syntax_Subst.shift_subst (n_us + n_binders)))
in ((uu____30031), (uu____30036))))
in (match (uu____30022) with
| (univs_opening1, univs_closing1) -> begin
(

let t2 = (

let uu____30060 = (FStar_Syntax_Subst.subst b_opening1 t1)
in (FStar_Syntax_Subst.subst univs_opening1 uu____30060))
in (

let uu____30061 = (elim_uvars_aux_t env [] [] t2)
in (match (uu____30061) with
| (uu____30088, uu____30089, t3) -> begin
(

let t4 = (

let uu____30112 = (

let uu____30113 = (FStar_Syntax_Subst.close_univ_vars us1 t3)
in (FStar_Syntax_Subst.subst b_closing1 uu____30113))
in (FStar_Syntax_Subst.subst univs_closing1 uu____30112))
in ((us1), (t4)))
end)))
end))
end))
end)))
end))
in (

let elim_term = (fun t -> (

let uu____30122 = (elim_uvars_aux_t env univs1 binders t)
in (match (uu____30122) with
| (uu____30141, uu____30142, t1) -> begin
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
| uu____30218 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((a.FStar_Syntax_Syntax.action_params), (body), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
end))
in (

let destruct_action_body = (fun body -> (

let uu____30245 = (

let uu____30246 = (FStar_Syntax_Subst.compress body)
in uu____30246.FStar_Syntax_Syntax.n)
in (match (uu____30245) with
| FStar_Syntax_Syntax.Tm_ascribed (defn, (FStar_Util.Inl (typ), FStar_Pervasives_Native.None), FStar_Pervasives_Native.None) -> begin
((defn), (typ))
end
| uu____30305 -> begin
(failwith "Impossible")
end)))
in (

let destruct_action_typ_templ = (fun t -> (

let uu____30339 = (

let uu____30340 = (FStar_Syntax_Subst.compress t)
in uu____30340.FStar_Syntax_Syntax.n)
in (match (uu____30339) with
| FStar_Syntax_Syntax.Tm_abs (pars, body, uu____30363) -> begin
(

let uu____30388 = (destruct_action_body body)
in (match (uu____30388) with
| (defn, typ) -> begin
((pars), (defn), (typ))
end))
end
| uu____30437 -> begin
(

let uu____30438 = (destruct_action_body t)
in (match (uu____30438) with
| (defn, typ) -> begin
(([]), (defn), (typ))
end))
end)))
in (

let uu____30493 = (elim_tscheme ((a.FStar_Syntax_Syntax.action_univs), (action_typ_templ)))
in (match (uu____30493) with
| (action_univs, t) -> begin
(

let uu____30502 = (destruct_action_typ_templ t)
in (match (uu____30502) with
| (action_params, action_defn, action_typ) -> begin
(

let a' = (

let uu___3713_30549 = a
in {FStar_Syntax_Syntax.action_name = uu___3713_30549.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___3713_30549.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action_univs; FStar_Syntax_Syntax.action_params = action_params; FStar_Syntax_Syntax.action_defn = action_defn; FStar_Syntax_Syntax.action_typ = action_typ})
in a')
end))
end))))))
in (

let ed1 = (

let uu___3716_30551 = ed
in (

let uu____30552 = (elim_tscheme ed.FStar_Syntax_Syntax.signature)
in (

let uu____30553 = (FStar_Syntax_Util.apply_eff_combinators elim_tscheme ed.FStar_Syntax_Syntax.combinators)
in (

let uu____30554 = (FStar_List.map elim_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.mname = uu___3716_30551.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.cattributes = uu___3716_30551.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = uu____30552; FStar_Syntax_Syntax.combinators = uu____30553; FStar_Syntax_Syntax.actions = uu____30554; FStar_Syntax_Syntax.eff_attrs = uu___3716_30551.FStar_Syntax_Syntax.eff_attrs}))))
in (

let uu___3719_30557 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ed1); FStar_Syntax_Syntax.sigrng = uu___3719_30557.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3719_30557.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3719_30557.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3719_30557.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___3719_30557.FStar_Syntax_Syntax.sigopts})))))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub_eff) -> begin
(

let elim_tscheme_opt = (fun uu___19_30578 -> (match (uu___19_30578) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (us, t) -> begin
(

let uu____30609 = (elim_uvars_aux_t env us [] t)
in (match (uu____30609) with
| (us1, uu____30641, t1) -> begin
FStar_Pervasives_Native.Some (((us1), (t1)))
end))
end))
in (

let sub_eff1 = (

let uu___3734_30672 = sub_eff
in (

let uu____30673 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp)
in (

let uu____30676 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift)
in {FStar_Syntax_Syntax.source = uu___3734_30672.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___3734_30672.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = uu____30673; FStar_Syntax_Syntax.lift = uu____30676})))
in (

let uu___3737_30679 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub_eff1); FStar_Syntax_Syntax.sigrng = uu___3737_30679.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3737_30679.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3737_30679.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3737_30679.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___3737_30679.FStar_Syntax_Syntax.sigopts})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univ_names, binders, comp, flags) -> begin
(

let uu____30689 = (elim_uvars_aux_c env univ_names binders comp)
in (match (uu____30689) with
| (univ_names1, binders1, comp1) -> begin
(

let uu___3750_30729 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (univ_names1), (binders1), (comp1), (flags))); FStar_Syntax_Syntax.sigrng = uu___3750_30729.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3750_30729.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3750_30729.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3750_30729.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___3750_30729.FStar_Syntax_Syntax.sigopts})
end))
end
| FStar_Syntax_Syntax.Sig_pragma (uu____30732) -> begin
s
end
| FStar_Syntax_Syntax.Sig_splice (uu____30733) -> begin
s
end))


let erase_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env t))


let unfold_head_once : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env t -> (

let aux = (fun f us args -> (

let uu____30782 = (FStar_TypeChecker_Env.lookup_nonrec_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]) env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____30782) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (head_def_ts) -> begin
(

let uu____30804 = (FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us)
in (match (uu____30804) with
| (uu____30811, head_def) -> begin
(

let t' = (FStar_Syntax_Syntax.mk_Tm_app head_def args FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let t'1 = (normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::[]) env t')
in FStar_Pervasives_Native.Some (t'1)))
end))
end)))
in (

let uu____30817 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____30817) with
| (head1, args) -> begin
(

let uu____30862 = (

let uu____30863 = (FStar_Syntax_Subst.compress head1)
in uu____30863.FStar_Syntax_Syntax.n)
in (match (uu____30862) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(aux fv [] args)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____30870; FStar_Syntax_Syntax.vars = uu____30871}, us) -> begin
(aux fv us args)
end
| uu____30877 -> begin
FStar_Pervasives_Native.None
end))
end))))




