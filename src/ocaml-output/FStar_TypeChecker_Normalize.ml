
open Prims
open FStar_Pervasives

let cases : 'Auu____11 'Auu____12 . ('Auu____11  ->  'Auu____12)  ->  'Auu____12  ->  'Auu____11 FStar_Pervasives_Native.option  ->  'Auu____12 = (fun f d uu___258_32 -> (match (uu___258_32) with
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
| uu____124 -> begin
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
| uu____228 -> begin
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
| uu____241 -> begin
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
| uu____415 -> begin
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
| uu____453 -> begin
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
| uu____491 -> begin
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
| uu____564 -> begin
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
| uu____672 -> begin
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
| uu____716 -> begin
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
| uu____756 -> begin
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
| uu____794 -> begin
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
| uu____812 -> begin
false
end))


let __proj__Debug__item___0 : stack_elt  ->  (FStar_Syntax_Syntax.term * FStar_Util.time) = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
_0
end))


type stack =
stack_elt Prims.list


let head_of : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____839 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____839) with
| (hd1, uu____855) -> begin
hd1
end)))


let mk : 'Auu____882 . 'Auu____882  ->  FStar_Range.range  ->  'Auu____882 FStar_Syntax_Syntax.syntax = (fun t r -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r))


let set_memo : 'a . FStar_TypeChecker_Cfg.cfg  ->  'a FStar_Syntax_Syntax.memo  ->  'a  ->  unit = (fun cfg r t -> (match (cfg.FStar_TypeChecker_Cfg.memoize_lazy) with
| true -> begin
(

let uu____945 = (FStar_ST.op_Bang r)
in (match (uu____945) with
| FStar_Pervasives_Native.Some (uu____993) -> begin
(failwith "Unexpected set_memo: thunk already evaluated")
end
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some (t)))
end))
end
| uu____1039 -> begin
()
end))


let rec env_to_string : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list  ->  Prims.string = (fun env -> (

let uu____1065 = (FStar_List.map (fun uu____1079 -> (match (uu____1079) with
| (bopt, c) -> begin
(

let uu____1092 = (match (bopt) with
| FStar_Pervasives_Native.None -> begin
"."
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.binder_to_string x)
end)
in (

let uu____1094 = (closure_to_string c)
in (FStar_Util.format2 "(%s, %s)" uu____1092 uu____1094)))
end)) env)
in (FStar_All.pipe_right uu____1065 (FStar_String.concat "; "))))
and closure_to_string : closure  ->  Prims.string = (fun uu___259_1097 -> (match (uu___259_1097) with
| Clos (env, t, uu____1100, uu____1101) -> begin
(

let uu____1146 = (FStar_All.pipe_right (FStar_List.length env) FStar_Util.string_of_int)
in (

let uu____1153 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "(env=%s elts; %s)" uu____1146 uu____1153)))
end
| Univ (uu____1154) -> begin
"Univ"
end
| Dummy -> begin
"dummy"
end))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun uu___260_1159 -> (match (uu___260_1159) with
| Arg (c, uu____1161, uu____1162) -> begin
(

let uu____1163 = (closure_to_string c)
in (FStar_Util.format1 "Closure %s" uu____1163))
end
| MemoLazy (uu____1164) -> begin
"MemoLazy"
end
| Abs (uu____1171, bs, uu____1173, uu____1174, uu____1175) -> begin
(

let uu____1180 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" uu____1180))
end
| UnivArgs (uu____1187) -> begin
"UnivArgs"
end
| Match (uu____1194) -> begin
"Match"
end
| App (uu____1203, t, uu____1205, uu____1206) -> begin
(

let uu____1207 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "App %s" uu____1207))
end
| Meta (uu____1208, m, uu____1210) -> begin
"Meta"
end
| Let (uu____1211) -> begin
"Let"
end
| Cfg (uu____1220) -> begin
"Cfg"
end
| Debug (t, uu____1222) -> begin
(

let uu____1223 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Debug %s" uu____1223))
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (

let uu____1233 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right uu____1233 (FStar_String.concat "; "))))


let is_empty : 'Auu____1242 . 'Auu____1242 Prims.list  ->  Prims.bool = (fun uu___261_1249 -> (match (uu___261_1249) with
| [] -> begin
true
end
| uu____1252 -> begin
false
end))


let lookup_bvar : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.bv  ->  closure = (fun env x -> (FStar_All.try_with (fun uu___280_1283 -> (match (()) with
| () -> begin
(

let uu____1284 = (FStar_List.nth env x.FStar_Syntax_Syntax.index)
in (FStar_Pervasives_Native.snd uu____1284))
end)) (fun uu___279_1301 -> (

let uu____1302 = (

let uu____1303 = (FStar_Syntax_Print.db_to_string x)
in (

let uu____1304 = (env_to_string env)
in (FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1303 uu____1304)))
in (failwith uu____1302)))))


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun l -> (

let uu____1312 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid)
in (match (uu____1312) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Pure_lid)
end
| uu____1315 -> begin
(

let uu____1316 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid)
in (match (uu____1316) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Tot_lid)
end
| uu____1319 -> begin
(

let uu____1320 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid)
in (match (uu____1320) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_PURE_lid)
end
| uu____1323 -> begin
FStar_Pervasives_Native.None
end))
end))
end)))


let norm_universe : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us1 = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let uu____1354 = (FStar_List.fold_left (fun uu____1380 u1 -> (match (uu____1380) with
| (cur_kernel, cur_max, out) -> begin
(

let uu____1405 = (FStar_Syntax_Util.univ_kernel u1)
in (match (uu____1405) with
| (k_u, n1) -> begin
(

let uu____1420 = (FStar_Syntax_Util.eq_univs cur_kernel k_u)
in (match (uu____1420) with
| true -> begin
((cur_kernel), (u1), (out))
end
| uu____1431 -> begin
((k_u), (u1), ((cur_max)::out))
end))
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us1)
in (match (uu____1354) with
| (uu____1438, u1, out) -> begin
(FStar_List.rev ((u1)::out))
end))))
in (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(FStar_All.try_with (fun uu___282_1463 -> (match (()) with
| () -> begin
(

let uu____1466 = (

let uu____1467 = (FStar_List.nth env x)
in (FStar_Pervasives_Native.snd uu____1467))
in (match (uu____1466) with
| Univ (u3) -> begin
((

let uu____1486 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv) (FStar_Options.Other ("univ_norm")))
in (match (uu____1486) with
| true -> begin
(

let uu____1487 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.print1 "Univ (in norm_universe): %s\n" uu____1487))
end
| uu____1488 -> begin
()
end));
(aux u3);
)
end
| Dummy -> begin
(u2)::[]
end
| uu____1489 -> begin
(

let uu____1490 = (

let uu____1491 = (FStar_Util.string_of_int x)
in (FStar_Util.format1 "Impossible: universe variable u@%s bound to a term" uu____1491))
in (failwith uu____1490))
end))
end)) (fun uu___281_1496 -> (match (uu___281_1496) with
| uu____1499 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.allow_unbound_universes) with
| true -> begin
(FStar_Syntax_Syntax.U_unknown)::[]
end
| uu____1502 -> begin
(

let uu____1503 = (

let uu____1504 = (FStar_Util.string_of_int x)
in (Prims.strcat "Universe variable not found: u@" uu____1504))
in (failwith uu____1503))
end)
end)))
end
| FStar_Syntax_Syntax.U_unif (uu____1507) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_zero -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_unif (uu____1516) -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_name (uu____1525) -> begin
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

let uu____1532 = (FStar_List.collect aux us)
in (FStar_All.pipe_right uu____1532 norm_univs))
in (match (us1) with
| (u_k)::(hd1)::rest -> begin
(

let rest1 = (hd1)::rest
in (

let uu____1549 = (FStar_Syntax_Util.univ_kernel u_k)
in (match (uu____1549) with
| (FStar_Syntax_Syntax.U_zero, n1) -> begin
(

let uu____1557 = (FStar_All.pipe_right rest1 (FStar_List.for_all (fun u3 -> (

let uu____1565 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____1565) with
| (uu____1570, m) -> begin
(n1 <= m)
end)))))
in (match (uu____1557) with
| true -> begin
rest1
end
| uu____1574 -> begin
us1
end))
end
| uu____1575 -> begin
us1
end)))
end
| uu____1580 -> begin
us1
end))
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1584 = (aux u3)
in (FStar_List.map (fun _0_1 -> FStar_Syntax_Syntax.U_succ (_0_1)) uu____1584))
end)))
in (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.erase_universes) with
| true -> begin
FStar_Syntax_Syntax.U_unknown
end
| uu____1587 -> begin
(

let uu____1588 = (aux u)
in (match (uu____1588) with
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


let rec inline_closure_env : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env stack t -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____1756 -> (

let uu____1757 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1758 = (env_to_string env)
in (

let uu____1759 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n" uu____1757 uu____1758 uu____1759))))));
(match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars) -> begin
(rebuild_closure cfg env stack t)
end
| uu____1768 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1771) -> begin
(

let uu____1794 = (FStar_Syntax_Subst.compress t)
in (inline_closure_env cfg env stack uu____1794))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1795) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_name (uu____1796) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_lazy (uu____1797) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1798) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_uvar (uv, s) -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____1822) -> begin
(

let uu____1835 = (

let uu____1836 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____1837 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s): CheckNoUvars: Unexpected unification variable remains: %s" uu____1836 uu____1837)))
in (failwith uu____1835))
end
| uu____1840 -> begin
(inline_closure_env cfg env stack t1)
end))
end
| uu____1841 -> begin
(

let s' = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (fun s1 -> (FStar_All.pipe_right s1 (FStar_List.map (fun uu___262_1875 -> (match (uu___262_1875) with
| FStar_Syntax_Syntax.NT (x, t1) -> begin
(

let uu____1882 = (

let uu____1889 = (inline_closure_env cfg env [] t1)
in ((x), (uu____1889)))
in FStar_Syntax_Syntax.NT (uu____1882))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let x_i = (FStar_Syntax_Syntax.bv_to_tm (

let uu___283_1899 = x
in {FStar_Syntax_Syntax.ppname = uu___283_1899.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___283_1899.FStar_Syntax_Syntax.sort}))
in (

let t1 = (inline_closure_env cfg env [] x_i)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x_j) -> begin
FStar_Syntax_Syntax.NM (((x), (x_j.FStar_Syntax_Syntax.index)))
end
| uu____1904 -> begin
FStar_Syntax_Syntax.NT (((x), (t1)))
end)))
end
| uu____1907 -> begin
(failwith "Impossible: subst invariant of uvar nodes")
end)))))))
in (

let t1 = (

let uu___284_1911 = t
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (((uv), (((s'), ((FStar_Pervasives_Native.snd s)))))); FStar_Syntax_Syntax.pos = uu___284_1911.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___284_1911.FStar_Syntax_Syntax.vars})
in (rebuild_closure cfg env stack t1)))
end)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let t1 = (

let uu____1932 = (

let uu____1933 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (uu____1933))
in (mk uu____1932 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env stack t1))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let t1 = (

let uu____1941 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1941))
in (rebuild_closure cfg env stack t1))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____1943 = (lookup_bvar env x)
in (match (uu____1943) with
| Univ (uu____1946) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(

let x1 = (

let uu___285_1950 = x
in {FStar_Syntax_Syntax.ppname = uu___285_1950.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___285_1950.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun})
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_bvar (x1)) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env stack t1)))
end
| Clos (env1, t0, uu____1956, uu____1957) -> begin
(inline_closure_env cfg env1 stack t0)
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____2046 stack1 -> (match (uu____2046) with
| (a, aq) -> begin
(

let uu____2058 = (

let uu____2059 = (

let uu____2066 = (

let uu____2067 = (

let uu____2098 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____2098), (false)))
in Clos (uu____2067))
in ((uu____2066), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (uu____2059))
in (uu____2058)::stack1)
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

let uu____2286 = (close_binders cfg env bs)
in (match (uu____2286) with
| (bs1, env') -> begin
(

let c1 = (close_comp cfg env' c)
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_arrow (((bs1), (c1)))) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env stack t1)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____2341 = (

let uu____2354 = (

let uu____2363 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2363)::[])
in (close_binders cfg env uu____2354))
in (match (uu____2341) with
| (x1, env1) -> begin
(

let phi1 = (non_tail_inline_closure_env cfg env1 phi)
in (

let t1 = (

let uu____2408 = (

let uu____2409 = (

let uu____2416 = (

let uu____2417 = (FStar_List.hd x1)
in (FStar_All.pipe_right uu____2417 FStar_Pervasives_Native.fst))
in ((uu____2416), (phi1)))
in FStar_Syntax_Syntax.Tm_refine (uu____2409))
in (mk uu____2408 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env1 stack t1)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, (annot, tacopt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____2516 = (non_tail_inline_closure_env cfg env t2)
in FStar_Util.Inl (uu____2516))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2530 = (close_comp cfg env c)
in FStar_Util.Inr (uu____2530))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (non_tail_inline_closure_env cfg env))
in (

let t2 = (

let uu____2549 = (

let uu____2550 = (

let uu____2577 = (non_tail_inline_closure_env cfg env t1)
in ((uu____2577), (((annot1), (tacopt1))), (lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2550))
in (mk uu____2549 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env stack t2))))
end
| FStar_Syntax_Syntax.Tm_quoted (t', qi) -> begin
(

let t1 = (match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____2623 = (

let uu____2624 = (

let uu____2631 = (non_tail_inline_closure_env cfg env t')
in ((uu____2631), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____2624))
in (mk uu____2623 t.FStar_Syntax_Syntax.pos))
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

let env1 = (FStar_List.fold_left (fun env1 uu____2683 -> (dummy)::env1) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (non_tail_inline_closure_env cfg env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (non_tail_inline_closure_env cfg env1 lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____2704 = (

let uu____2715 = (FStar_Syntax_Syntax.is_top_level ((lb)::[]))
in (match (uu____2715) with
| true -> begin
((lb.FStar_Syntax_Syntax.lbname), (body))
end
| uu____2732 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2734 = (non_tail_inline_closure_env cfg ((dummy)::env0) body)
in ((FStar_Util.Inl ((

let uu___286_2750 = x
in {FStar_Syntax_Syntax.ppname = uu___286_2750.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___286_2750.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = typ}))), (uu____2734))))
end))
in (match (uu____2704) with
| (nm, body1) -> begin
(

let lb1 = (

let uu___287_2768 = lb
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___287_2768.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = uu___287_2768.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___287_2768.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___287_2768.FStar_Syntax_Syntax.lbpos})
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (body1)))) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env0 stack t1)))
end))))))
end
| FStar_Syntax_Syntax.Tm_let ((uu____2782, lbs), body) -> begin
(

let norm_one_lb = (fun env1 lb -> (

let env_univs = (FStar_List.fold_right (fun uu____2845 env2 -> (dummy)::env2) lb.FStar_Syntax_Syntax.lbunivs env1)
in (

let env2 = (

let uu____2862 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____2862) with
| true -> begin
env_univs
end
| uu____2863 -> begin
(FStar_List.fold_right (fun uu____2874 env2 -> (dummy)::env2) lbs env_univs)
end))
in (

let ty = (non_tail_inline_closure_env cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (

let nm = (

let uu____2898 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____2898) with
| true -> begin
lb.FStar_Syntax_Syntax.lbname
end
| uu____2903 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in FStar_Util.Inl ((

let uu___288_2906 = x
in {FStar_Syntax_Syntax.ppname = uu___288_2906.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___288_2906.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
end))
in (

let uu___289_2907 = lb
in (

let uu____2908 = (non_tail_inline_closure_env cfg env2 lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___289_2907.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___289_2907.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____2908; FStar_Syntax_Syntax.lbattrs = uu___289_2907.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___289_2907.FStar_Syntax_Syntax.lbpos})))))))
in (

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body1 = (

let body_env = (FStar_List.fold_right (fun uu____2940 env1 -> (dummy)::env1) lbs1 env)
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
and rebuild_closure : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env stack t -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____3029 -> (

let uu____3030 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____3031 = (env_to_string env)
in (

let uu____3032 = (stack_to_string stack)
in (

let uu____3033 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print4 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n" uu____3030 uu____3031 uu____3032 uu____3033)))))));
(match (stack) with
| [] -> begin
t
end
| (Arg (Clos (env_arg, tm, uu____3038, uu____3039), aq, r))::stack1 -> begin
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

let uu____3118 = (close_binders cfg env' bs)
in (match (uu____3118) with
| (bs1, uu____3134) -> begin
(

let lopt1 = (close_lcomp_opt cfg env'' lopt)
in (

let uu____3154 = (

let uu___290_3157 = (FStar_Syntax_Util.abs bs1 t lopt1)
in {FStar_Syntax_Syntax.n = uu___290_3157.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___290_3157.FStar_Syntax_Syntax.vars})
in (rebuild_closure cfg env stack1 uu____3154)))
end))
end
| (Match (env1, branches, cfg1, r))::stack1 -> begin
(

let close_one_branch = (fun env2 uu____3213 -> (match (uu____3213) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env3 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____3328) -> begin
((p), (env3))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3357 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____3441 uu____3442 -> (match (((uu____3441), (uu____3442))) with
| ((pats1, env4), (p1, b)) -> begin
(

let uu____3581 = (norm_pat env4 p1)
in (match (uu____3581) with
| (p2, env5) -> begin
(((((p2), (b)))::pats1), (env5))
end))
end)) (([]), (env3))))
in (match (uu____3357) with
| (pats1, env4) -> begin
(((

let uu___291_3743 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___291_3743.FStar_Syntax_Syntax.p})), (env4))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___292_3762 = x
in (

let uu____3763 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___292_3762.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___292_3762.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3763}))
in (((

let uu___293_3777 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___293_3777.FStar_Syntax_Syntax.p})), ((dummy)::env3)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___294_3788 = x
in (

let uu____3789 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___294_3788.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___294_3788.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3789}))
in (((

let uu___295_3803 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___295_3803.FStar_Syntax_Syntax.p})), ((dummy)::env3)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t1) -> begin
(

let x1 = (

let uu___296_3819 = x
in (

let uu____3820 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___296_3819.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___296_3819.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3820}))
in (

let t2 = (non_tail_inline_closure_env cfg1 env3 t1)
in (((

let uu___297_3837 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t2))); FStar_Syntax_Syntax.p = uu___297_3837.FStar_Syntax_Syntax.p})), (env3))))
end))
in (

let uu____3842 = (norm_pat env2 pat)
in (match (uu____3842) with
| (pat1, env3) -> begin
(

let w_opt1 = (match (w_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____3911 = (non_tail_inline_closure_env cfg1 env3 w)
in FStar_Pervasives_Native.Some (uu____3911))
end)
in (

let tm1 = (non_tail_inline_closure_env cfg1 env3 tm)
in ((pat1), (w_opt1), (tm1))))
end)))
end))
in (

let t1 = (

let uu____3930 = (

let uu____3931 = (

let uu____3954 = (FStar_All.pipe_right branches (FStar_List.map (close_one_branch env1)))
in ((t), (uu____3954)))
in FStar_Syntax_Syntax.Tm_match (uu____3931))
in (mk uu____3930 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg1 env1 stack1 t1)))
end
| (Meta (env_m, m, r))::stack1 -> begin
(

let m1 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let uu____4069 = (FStar_All.pipe_right args (FStar_List.map (fun args1 -> (FStar_All.pipe_right args1 (FStar_List.map (fun uu____4178 -> (match (uu____4178) with
| (a, q) -> begin
(

let uu____4205 = (non_tail_inline_closure_env cfg env_m a)
in ((uu____4205), (q)))
end)))))))
in FStar_Syntax_Syntax.Meta_pattern (uu____4069))
end
| FStar_Syntax_Syntax.Meta_monadic (m1, tbody) -> begin
(

let uu____4218 = (

let uu____4225 = (non_tail_inline_closure_env cfg env_m tbody)
in ((m1), (uu____4225)))
in FStar_Syntax_Syntax.Meta_monadic (uu____4218))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody) -> begin
(

let uu____4237 = (

let uu____4246 = (non_tail_inline_closure_env cfg env_m tbody)
in ((m1), (m2), (uu____4246)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____4237))
end
| uu____4251 -> begin
m
end)
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m1)))) r)
in (rebuild_closure cfg env stack1 t1)))
end
| uu____4257 -> begin
(failwith "Impossible: unexpected stack element")
end);
))
and close_imp : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun cfg env imp -> (match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____4272 = (

let uu____4273 = (inline_closure_env cfg env [] t)
in FStar_Syntax_Syntax.Meta (uu____4273))
in FStar_Pervasives_Native.Some (uu____4272))
end
| i -> begin
i
end))
and close_binders : FStar_TypeChecker_Cfg.cfg  ->  env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * env) = (fun cfg env bs -> (

let uu____4290 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____4374 uu____4375 -> (match (((uu____4374), (uu____4375))) with
| ((env1, out), (b, imp)) -> begin
(

let b1 = (

let uu___298_4515 = b
in (

let uu____4516 = (inline_closure_env cfg env1 [] b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___298_4515.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___298_4515.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4516}))
in (

let imp1 = (close_imp cfg env1 imp)
in (

let env2 = (dummy)::env1
in ((env2), ((((b1), (imp1)))::out)))))
end)) ((env), ([]))))
in (match (uu____4290) with
| (env1, bs1) -> begin
(((FStar_List.rev bs1)), (env1))
end)))
and close_comp : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars) -> begin
c
end
| uu____4656 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____4669 = (inline_closure_env cfg env [] t)
in (

let uu____4670 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____4669 uu____4670)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____4683 = (inline_closure_env cfg env [] t)
in (

let uu____4684 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____4683 uu____4684)))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let rt = (inline_closure_env cfg env [] c1.FStar_Syntax_Syntax.result_typ)
in (

let args = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun uu____4738 -> (match (uu____4738) with
| (a, q) -> begin
(

let uu____4759 = (inline_closure_env cfg env [] a)
in ((uu____4759), (q)))
end))))
in (

let flags1 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___263_4776 -> (match (uu___263_4776) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____4780 = (inline_closure_env cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____4780))
end
| f -> begin
f
end))))
in (

let uu____4784 = (

let uu___299_4785 = c1
in (

let uu____4786 = (FStar_List.map (norm_universe cfg env) c1.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = uu____4786; FStar_Syntax_Syntax.effect_name = uu___299_4785.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags1}))
in (FStar_Syntax_Syntax.mk_Comp uu____4784)))))
end)
end))
and filter_out_lcomp_cflags : FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun flags1 -> (FStar_All.pipe_right flags1 (FStar_List.filter (fun uu___264_4796 -> (match (uu___264_4796) with
| FStar_Syntax_Syntax.DECREASES (uu____4797) -> begin
false
end
| uu____4800 -> begin
true
end)))))
and close_lcomp_opt : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags1 = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.filter (fun uu___265_4818 -> (match (uu___265_4818) with
| FStar_Syntax_Syntax.DECREASES (uu____4819) -> begin
false
end
| uu____4822 -> begin
true
end))))
in (

let rc1 = (

let uu___300_4824 = rc
in (

let uu____4825 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inline_closure_env cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___300_4824.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____4825; FStar_Syntax_Syntax.residual_flags = flags1}))
in FStar_Pervasives_Native.Some (rc1)))
end
| uu____4834 -> begin
lopt
end))


let closure_as_term : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (non_tail_inline_closure_env cfg env t))


let unembed_binder_knot : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let unembed_binder : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option = (fun t -> (

let uu____4901 = (FStar_ST.op_Bang unembed_binder_knot)
in (match (uu____4901) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____4940 = (FStar_Syntax_Embeddings.unembed e t)
in (uu____4940 true FStar_Syntax_Embeddings.id_norm_cb))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_UnembedBinderKnot), ("unembed_binder_knot is unset!")));
FStar_Pervasives_Native.None;
)
end)))


let mk_psc_subst : 'Auu____4960 . FStar_TypeChecker_Cfg.cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____4960) FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun cfg env -> (FStar_List.fold_right (fun uu____5022 subst1 -> (match (uu____5022) with
| (binder_opt, closure) -> begin
(match (((binder_opt), (closure))) with
| (FStar_Pervasives_Native.Some (b), Clos (env1, term, uu____5063, uu____5064)) -> begin
(

let uu____5123 = b
in (match (uu____5123) with
| (bv, uu____5131) -> begin
(

let uu____5132 = (

let uu____5133 = (FStar_Syntax_Util.is_constructed_typ bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.binder_lid)
in (not (uu____5133)))
in (match (uu____5132) with
| true -> begin
subst1
end
| uu____5136 -> begin
(

let term1 = (closure_as_term cfg env1 term)
in (

let uu____5138 = (unembed_binder term1)
in (match (uu____5138) with
| FStar_Pervasives_Native.None -> begin
subst1
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let b1 = (

let uu____5145 = (

let uu___301_5146 = bv
in (

let uu____5147 = (FStar_Syntax_Subst.subst subst1 (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___301_5146.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___301_5146.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5147}))
in (FStar_Syntax_Syntax.freshen_bv uu____5145))
in (

let b_for_x = (

let uu____5153 = (

let uu____5160 = (FStar_Syntax_Syntax.bv_to_name b1)
in (((FStar_Pervasives_Native.fst x)), (uu____5160)))
in FStar_Syntax_Syntax.NT (uu____5153))
in (

let subst2 = (FStar_List.filter (fun uu___266_5176 -> (match (uu___266_5176) with
| FStar_Syntax_Syntax.NT (uu____5177, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (b'); FStar_Syntax_Syntax.pos = uu____5179; FStar_Syntax_Syntax.vars = uu____5180}) -> begin
(

let uu____5185 = (FStar_Ident.ident_equals b1.FStar_Syntax_Syntax.ppname b'.FStar_Syntax_Syntax.ppname)
in (not (uu____5185)))
end
| uu____5186 -> begin
true
end)) subst1)
in (b_for_x)::subst2)))
end)))
end))
end))
end
| uu____5187 -> begin
subst1
end)
end)) env []))


let reduce_primops : 'Auu____5209 . FStar_Syntax_Embeddings.norm_cb  ->  FStar_TypeChecker_Cfg.cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____5209) FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun norm_cb cfg env tm -> (match ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.primops))) with
| true -> begin
tm
end
| uu____5260 -> begin
(

let uu____5261 = (FStar_Syntax_Util.head_and_args tm)
in (match (uu____5261) with
| (head1, args) -> begin
(

let uu____5306 = (

let uu____5307 = (FStar_Syntax_Util.un_uinst head1)
in uu____5307.FStar_Syntax_Syntax.n)
in (match (uu____5306) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5313 = (FStar_TypeChecker_Cfg.find_prim_step cfg fv)
in (match (uu____5313) with
| FStar_Pervasives_Native.Some (prim_step) when (prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok || (not (cfg.FStar_TypeChecker_Cfg.strong))) -> begin
(

let l = (FStar_List.length args)
in (match ((l < prim_step.FStar_TypeChecker_Cfg.arity)) with
| true -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5341 -> (

let uu____5342 = (FStar_Syntax_Print.lid_to_string prim_step.FStar_TypeChecker_Cfg.name)
in (

let uu____5343 = (FStar_Util.string_of_int l)
in (

let uu____5350 = (FStar_Util.string_of_int prim_step.FStar_TypeChecker_Cfg.arity)
in (FStar_Util.print3 "primop: found partially applied %s (%s/%s args)\n" uu____5342 uu____5343 uu____5350))))));
tm;
)
end
| uu____5351 -> begin
(

let uu____5352 = (match ((Prims.op_Equality l prim_step.FStar_TypeChecker_Cfg.arity)) with
| true -> begin
((args), ([]))
end
| uu____5403 -> begin
(FStar_List.splitAt prim_step.FStar_TypeChecker_Cfg.arity args)
end)
in (match (uu____5352) with
| (args_1, args_2) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5439 -> (

let uu____5440 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: trying to reduce <%s>\n" uu____5440))));
(

let psc = {FStar_TypeChecker_Cfg.psc_range = head1.FStar_Syntax_Syntax.pos; FStar_TypeChecker_Cfg.psc_subst = (fun uu____5443 -> (match (prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution) with
| true -> begin
(mk_psc_subst cfg env)
end
| uu____5444 -> begin
[]
end))}
in (

let r = (prim_step.FStar_TypeChecker_Cfg.interpretation psc norm_cb args_1)
in (match (r) with
| FStar_Pervasives_Native.None -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5457 -> (

let uu____5458 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: <%s> did not reduce\n" uu____5458))));
tm;
)
end
| FStar_Pervasives_Native.Some (reduced) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5464 -> (

let uu____5465 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____5466 = (FStar_Syntax_Print.term_to_string reduced)
in (FStar_Util.print2 "primop: <%s> reduced to <%s>\n" uu____5465 uu____5466)))));
(FStar_Syntax_Util.mk_app reduced args_2);
)
end)));
)
end))
end))
end
| FStar_Pervasives_Native.Some (uu____5467) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5471 -> (

let uu____5472 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: not reducing <%s> since we\'re doing strong reduction\n" uu____5472))));
tm;
)
end
| FStar_Pervasives_Native.None -> begin
tm
end))
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of) when (not (cfg.FStar_TypeChecker_Cfg.strong)) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5476 -> (

let uu____5477 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: reducing <%s>\n" uu____5477))));
(match (args) with
| ((a1, uu____5481))::[] -> begin
(FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range a1.FStar_Syntax_Syntax.pos tm.FStar_Syntax_Syntax.pos)
end
| uu____5506 -> begin
tm
end);
)
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of) when (not (cfg.FStar_TypeChecker_Cfg.strong)) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5520 -> (

let uu____5521 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: reducing <%s>\n" uu____5521))));
(match (args) with
| ((t, uu____5525))::((r, uu____5527))::[] -> begin
(

let uu____5568 = (FStar_TypeChecker_Cfg.try_unembed_simple FStar_Syntax_Embeddings.e_range r)
in (match (uu____5568) with
| FStar_Pervasives_Native.Some (rng) -> begin
(FStar_Syntax_Subst.set_use_range rng t)
end
| FStar_Pervasives_Native.None -> begin
tm
end))
end
| uu____5574 -> begin
tm
end);
)
end
| uu____5585 -> begin
tm
end))
end))
end))


let reduce_equality : 'Auu____5596 . FStar_Syntax_Embeddings.norm_cb  ->  FStar_TypeChecker_Cfg.cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____5596) FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun norm_cb cfg tm -> (reduce_primops norm_cb (

let uu___302_5649 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___303_5652 = FStar_TypeChecker_Cfg.default_steps
in {FStar_TypeChecker_Cfg.beta = uu___303_5652.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___303_5652.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___303_5652.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___303_5652.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___303_5652.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = true; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___303_5652.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___303_5652.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___303_5652.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___303_5652.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___303_5652.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___303_5652.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___303_5652.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___303_5652.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___303_5652.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___303_5652.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___303_5652.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___303_5652.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___303_5652.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___303_5652.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___303_5652.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___303_5652.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___303_5652.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___303_5652.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___303_5652.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___303_5652.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___302_5649.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___302_5649.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___302_5649.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = FStar_TypeChecker_Cfg.equality_ops; FStar_TypeChecker_Cfg.strong = uu___302_5649.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___302_5649.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___302_5649.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___302_5649.FStar_TypeChecker_Cfg.reifying}) tm))

type norm_request_t =
| Norm_request_none
| Norm_request_ready
| Norm_request_requires_rejig


let uu___is_Norm_request_none : norm_request_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Norm_request_none -> begin
true
end
| uu____5658 -> begin
false
end))


let uu___is_Norm_request_ready : norm_request_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Norm_request_ready -> begin
true
end
| uu____5664 -> begin
false
end))


let uu___is_Norm_request_requires_rejig : norm_request_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Norm_request_requires_rejig -> begin
true
end
| uu____5670 -> begin
false
end))


let is_norm_request : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  norm_request_t = (fun hd1 args -> (

let aux = (fun min_args -> (

let uu____5687 = (FStar_All.pipe_right args FStar_List.length)
in (FStar_All.pipe_right uu____5687 (fun n1 -> (match ((n1 < min_args)) with
| true -> begin
Norm_request_none
end
| uu____5708 -> begin
(match ((Prims.op_Equality n1 min_args)) with
| true -> begin
Norm_request_ready
end
| uu____5709 -> begin
Norm_request_requires_rejig
end)
end)))))
in (

let uu____5710 = (

let uu____5711 = (FStar_Syntax_Util.un_uinst hd1)
in uu____5711.FStar_Syntax_Syntax.n)
in (match (uu____5710) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term) -> begin
(aux (Prims.parse_int "2"))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize) -> begin
(aux (Prims.parse_int "1"))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm) -> begin
(aux (Prims.parse_int "3"))
end
| uu____5717 -> begin
Norm_request_none
end))))


let should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg  ->  Prims.bool = (fun cfg -> ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.no_full_norm)) && (

let uu____5724 = (FStar_Ident.lid_equals cfg.FStar_TypeChecker_Cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid)
in (not (uu____5724)))))


let rejig_norm_request : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term = (fun hd1 args -> (

let uu____5735 = (

let uu____5736 = (FStar_Syntax_Util.un_uinst hd1)
in uu____5736.FStar_Syntax_Syntax.n)
in (match (uu____5735) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term) -> begin
(match (args) with
| (t1)::(t2)::rest when ((FStar_List.length rest) > (Prims.parse_int "0")) -> begin
(

let uu____5793 = (FStar_Syntax_Util.mk_app hd1 ((t1)::(t2)::[]))
in (FStar_Syntax_Util.mk_app uu____5793 rest))
end
| uu____5820 -> begin
(failwith "Impossible! invalid rejig_norm_request for normalize_term")
end)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize) -> begin
(match (args) with
| (t)::rest when ((FStar_List.length rest) > (Prims.parse_int "0")) -> begin
(

let uu____5858 = (FStar_Syntax_Util.mk_app hd1 ((t)::[]))
in (FStar_Syntax_Util.mk_app uu____5858 rest))
end
| uu____5877 -> begin
(failwith "Impossible! invalid rejig_norm_request for normalize")
end)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm) -> begin
(match (args) with
| (t1)::(t2)::(t3)::rest when ((FStar_List.length rest) > (Prims.parse_int "0")) -> begin
(

let uu____5949 = (FStar_Syntax_Util.mk_app hd1 ((t1)::(t2)::(t3)::[]))
in (FStar_Syntax_Util.mk_app uu____5949 rest))
end
| uu____5984 -> begin
(failwith "Impossible! invalid rejig_norm_request for norm")
end)
end
| uu____5985 -> begin
(

let uu____5986 = (

let uu____5987 = (FStar_Syntax_Print.term_to_string hd1)
in (Prims.strcat "Impossible! invalid rejig_norm_request for: %s" uu____5987))
in (failwith uu____5986))
end)))


let is_nbe_request : FStar_TypeChecker_Env.step Prims.list  ->  Prims.bool = (fun s -> (FStar_Util.for_some (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s))


let tr_norm_step : FStar_Syntax_Embeddings.norm_step  ->  FStar_TypeChecker_Env.step Prims.list = (fun uu___267_6003 -> (match (uu___267_6003) with
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

let uu____6009 = (

let uu____6012 = (

let uu____6013 = (FStar_List.map FStar_Ident.lid_of_str names1)
in FStar_TypeChecker_Env.UnfoldOnly (uu____6013))
in (uu____6012)::[])
in (FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::uu____6009)
end
| FStar_Syntax_Embeddings.UnfoldFully (names1) -> begin
(

let uu____6019 = (

let uu____6022 = (

let uu____6023 = (FStar_List.map FStar_Ident.lid_of_str names1)
in FStar_TypeChecker_Env.UnfoldFully (uu____6023))
in (uu____6022)::[])
in (FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::uu____6019)
end
| FStar_Syntax_Embeddings.UnfoldAttr (names1) -> begin
(

let uu____6029 = (

let uu____6032 = (

let uu____6033 = (FStar_List.map FStar_Ident.lid_of_str names1)
in FStar_TypeChecker_Env.UnfoldAttr (uu____6033))
in (uu____6032)::[])
in (FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::uu____6029)
end
| FStar_Syntax_Embeddings.NBE -> begin
(FStar_TypeChecker_Env.NBE)::[]
end))


let tr_norm_steps : FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_TypeChecker_Env.step Prims.list = (fun s -> (FStar_List.concatMap tr_norm_step s))


let get_norm_request : 'Auu____6055 . FStar_TypeChecker_Cfg.cfg  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term * 'Auu____6055) Prims.list  ->  (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun cfg full_norm args -> (

let parse_steps = (fun s -> (

let uu____6106 = (

let uu____6111 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_norm_step)
in (FStar_TypeChecker_Cfg.try_unembed_simple uu____6111 s))
in (match (uu____6106) with
| FStar_Pervasives_Native.Some (steps) -> begin
(

let uu____6127 = (tr_norm_steps steps)
in FStar_Pervasives_Native.Some (uu____6127))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))
in (

let inherited_steps = (FStar_List.append (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.erase_universes) with
| true -> begin
(FStar_TypeChecker_Env.EraseUniverses)::[]
end
| uu____6141 -> begin
[]
end) (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.allow_unbound_universes) with
| true -> begin
(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]
end
| uu____6144 -> begin
[]
end))
in (match (args) with
| (uu____6153)::((tm, uu____6155))::[] -> begin
(

let s = (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Reify)::[]
in FStar_Pervasives_Native.Some ((((FStar_List.append inherited_steps s)), (tm))))
end
| ((tm, uu____6184))::[] -> begin
(

let s = (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Reify)::[]
in FStar_Pervasives_Native.Some ((((FStar_List.append inherited_steps s)), (tm))))
end
| ((steps, uu____6205))::(uu____6206)::((tm, uu____6208))::[] -> begin
(

let add_exclude = (fun s z -> (

let uu____6246 = (FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s)
in (match (uu____6246) with
| true -> begin
s
end
| uu____6249 -> begin
(FStar_TypeChecker_Env.Exclude (z))::s
end)))
in (

let uu____6250 = (

let uu____6255 = (full_norm steps)
in (parse_steps uu____6255))
in (match (uu____6250) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s) -> begin
(

let s1 = (FStar_TypeChecker_Env.Beta)::s
in (

let s2 = (add_exclude s1 FStar_TypeChecker_Env.Zeta)
in (

let s3 = (add_exclude s2 FStar_TypeChecker_Env.Iota)
in FStar_Pervasives_Native.Some ((((FStar_List.append inherited_steps s3)), (tm))))))
end)))
end
| uu____6294 -> begin
FStar_Pervasives_Native.None
end))))


let nbe_eval : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_Env.steps  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg s tm -> (

let delta_level = (

let uu____6325 = (FStar_All.pipe_right s (FStar_Util.for_some (fun uu___268_6330 -> (match (uu___268_6330) with
| FStar_TypeChecker_Env.UnfoldUntil (uu____6331) -> begin
true
end
| FStar_TypeChecker_Env.UnfoldOnly (uu____6332) -> begin
true
end
| FStar_TypeChecker_Env.UnfoldFully (uu____6335) -> begin
true
end
| uu____6338 -> begin
false
end))))
in (match (uu____6325) with
| true -> begin
(FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]
end
| uu____6341 -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end))
in ((FStar_TypeChecker_Cfg.log_nbe cfg (fun uu____6345 -> (

let uu____6346 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Invoking NBE with  %s\n" uu____6346))));
(

let tm_norm = (

let uu____6348 = (

let uu____6363 = (FStar_TypeChecker_Cfg.cfg_env cfg)
in uu____6363.FStar_TypeChecker_Env.nbe)
in (uu____6348 s cfg.FStar_TypeChecker_Cfg.tcenv tm))
in ((FStar_TypeChecker_Cfg.log_nbe cfg (fun uu____6367 -> (

let uu____6368 = (FStar_Syntax_Print.term_to_string tm_norm)
in (FStar_Util.print1 "Result of NBE is  %s\n" uu____6368))));
tm_norm;
));
)))


let is_reify_head : stack_elt Prims.list  ->  Prims.bool = (fun uu___269_6375 -> (match (uu___269_6375) with
| (App (uu____6378, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____6379; FStar_Syntax_Syntax.vars = uu____6380}, uu____6381, uu____6382))::uu____6383 -> begin
true
end
| uu____6388 -> begin
false
end))


let firstn : 'Auu____6397 . Prims.int  ->  'Auu____6397 Prims.list  ->  ('Auu____6397 Prims.list * 'Auu____6397 Prims.list) = (fun k l -> (match (((FStar_List.length l) < k)) with
| true -> begin
((l), ([]))
end
| uu____6424 -> begin
(FStar_Util.first_N k l)
end))


let should_reify : FStar_TypeChecker_Cfg.cfg  ->  stack_elt Prims.list  ->  Prims.bool = (fun cfg stack -> (

let rec drop_irrel = (fun uu___270_6448 -> (match (uu___270_6448) with
| (MemoLazy (uu____6453))::s -> begin
(drop_irrel s)
end
| (UnivArgs (uu____6463))::s -> begin
(drop_irrel s)
end
| s -> begin
s
end))
in (

let uu____6476 = (drop_irrel stack)
in (match (uu____6476) with
| (App (uu____6479, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____6480; FStar_Syntax_Syntax.vars = uu____6481}, uu____6482, uu____6483))::uu____6484 -> begin
cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.reify_
end
| uu____6489 -> begin
false
end))))


let rec maybe_weakly_reduced : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun tm -> (

let aux_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (t, uu____6512) -> begin
(maybe_weakly_reduced t)
end
| FStar_Syntax_Syntax.Total (t, uu____6522) -> begin
(maybe_weakly_reduced t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
((maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) || (FStar_Util.for_some (fun uu____6543 -> (match (uu____6543) with
| (a, uu____6553) -> begin
(maybe_weakly_reduced a)
end)) ct.FStar_Syntax_Syntax.effect_args))
end))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____6563) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (uu____6586) -> begin
false
end
| FStar_Syntax_Syntax.Tm_uvar (uu____6587) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____6600) -> begin
false
end
| FStar_Syntax_Syntax.Tm_bvar (uu____6601) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (uu____6602) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____6603) -> begin
false
end
| FStar_Syntax_Syntax.Tm_lazy (uu____6604) -> begin
false
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| FStar_Syntax_Syntax.Tm_uinst (uu____6605) -> begin
false
end
| FStar_Syntax_Syntax.Tm_quoted (uu____6612) -> begin
false
end
| FStar_Syntax_Syntax.Tm_let (uu____6619) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____6632) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____6651) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____6666) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____6673) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
((maybe_weakly_reduced t1) || (FStar_All.pipe_right args (FStar_Util.for_some (fun uu____6743 -> (match (uu____6743) with
| (a, uu____6753) -> begin
(maybe_weakly_reduced a)
end)))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____6764) -> begin
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
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(FStar_Util.for_some (FStar_Util.for_some (fun uu____6892 -> (match (uu____6892) with
| (a, uu____6902) -> begin
(maybe_weakly_reduced a)
end))) args)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____6911, uu____6912, t') -> begin
(maybe_weakly_reduced t')
end
| FStar_Syntax_Syntax.Meta_monadic (uu____6918, t') -> begin
(maybe_weakly_reduced t')
end
| FStar_Syntax_Syntax.Meta_labeled (uu____6924) -> begin
false
end
| FStar_Syntax_Syntax.Meta_desugared (uu____6931) -> begin
false
end
| FStar_Syntax_Syntax.Meta_named (uu____6932) -> begin
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
| uu____6938 -> begin
false
end))


let uu___is_Should_unfold_yes : should_unfold_res  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Should_unfold_yes -> begin
true
end
| uu____6944 -> begin
false
end))


let uu___is_Should_unfold_fully : should_unfold_res  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Should_unfold_fully -> begin
true
end
| uu____6950 -> begin
false
end))


let uu___is_Should_unfold_reify : should_unfold_res  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Should_unfold_reify -> begin
true
end
| uu____6956 -> begin
false
end))


let should_unfold : FStar_TypeChecker_Cfg.cfg  ->  (FStar_TypeChecker_Cfg.cfg  ->  Prims.bool)  ->  FStar_Syntax_Syntax.fv  ->  FStar_TypeChecker_Env.qninfo  ->  should_unfold_res = (fun cfg should_reify1 fv qninfo -> (

let attrs = (

let uu____6985 = (FStar_TypeChecker_Env.attrs_of_qninfo qninfo)
in (match (uu____6985) with
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
| uu____7045 -> begin
no
end))
in (

let fullyno = (fun b -> (match (b) with
| true -> begin
fully
end
| uu____7064 -> begin
no
end))
in (

let comb_or = (fun l -> (FStar_List.fold_right (fun uu____7113 uu____7114 -> (match (((uu____7113), (uu____7114))) with
| ((a, b, c), (x, y, z)) -> begin
(((a || x)), ((b || y)), ((c || z)))
end)) l ((false), (false), (false))))
in (

let string_of_res = (fun uu____7174 -> (match (uu____7174) with
| (x, y, z) -> begin
(

let uu____7184 = (FStar_Util.string_of_bool x)
in (

let uu____7185 = (FStar_Util.string_of_bool y)
in (

let uu____7186 = (FStar_Util.string_of_bool z)
in (FStar_Util.format3 "(%s,%s,%s)" uu____7184 uu____7185 uu____7186))))
end))
in (

let res = if (FStar_TypeChecker_Env.qninfo_is_action qninfo) then begin
(

let b = (should_reify1 cfg)
in ((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7205 -> (

let uu____7206 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____7207 = (FStar_Util.string_of_bool b)
in (FStar_Util.print2 "should_unfold: For DM4F action %s, should_reify = %s\n" uu____7206 uu____7207)))));
(match (b) with
| true -> begin
reif
end
| uu____7214 -> begin
no
end);
))
end else begin
if (

let uu____7215 = (FStar_TypeChecker_Cfg.find_prim_step cfg fv)
in (FStar_Option.isSome uu____7215)) then begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7220 -> (FStar_Util.print_string " >> It\'s a primop, not unfolding\n")));
no;
)
end else begin
(match (((qninfo), (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_only), (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_fully), (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_attr))) with
| (FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, uu____7254), uu____7255); FStar_Syntax_Syntax.sigrng = uu____7256; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____7258; FStar_Syntax_Syntax.sigattrs = uu____7259}, uu____7260), uu____7261), uu____7262, uu____7263, uu____7264) when (FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect qs) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7369 -> (FStar_Util.print_string " >> HasMaskedEffect, not unfolding\n")));
no;
)
end
| (uu____7370, uu____7371, uu____7372, uu____7373) when (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_tac && (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.tac_opaque_attr) attrs)) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7440 -> (FStar_Util.print_string " >> tac_opaque, not unfolding\n")));
no;
)
end
| (FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, uu____7442), uu____7443); FStar_Syntax_Syntax.sigrng = uu____7444; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____7446; FStar_Syntax_Syntax.sigattrs = uu____7447}, uu____7448), uu____7449), uu____7450, uu____7451, uu____7452) when (is_rec && (not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta))) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7557 -> (FStar_Util.print_string " >> It\'s a recursive definition but we\'re not doing Zeta, not unfolding\n")));
no;
)
end
| (uu____7558, FStar_Pervasives_Native.Some (uu____7559), uu____7560, uu____7561) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7629 -> (

let uu____7630 = (FStar_Syntax_Print.fv_to_string fv)
in (FStar_Util.print1 "should_unfold: Reached a %s with selective unfolding\n" uu____7630))));
(

let uu____7631 = (

let uu____7640 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_only) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____7660 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left yesno uu____7660))
end)
in (

let uu____7667 = (

let uu____7676 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_attr) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____7696 = (FStar_Util.for_some (fun at -> (FStar_Util.for_some (fun lid -> (FStar_Syntax_Util.is_fvar lid at)) lids)) attrs)
in (FStar_All.pipe_left yesno uu____7696))
end)
in (

let uu____7707 = (

let uu____7716 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_fully) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____7736 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left fullyno uu____7736))
end)
in (uu____7716)::[])
in (uu____7676)::uu____7707))
in (uu____7640)::uu____7667))
in (comb_or uu____7631));
)
end
| (uu____7767, uu____7768, FStar_Pervasives_Native.Some (uu____7769), uu____7770) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7838 -> (

let uu____7839 = (FStar_Syntax_Print.fv_to_string fv)
in (FStar_Util.print1 "should_unfold: Reached a %s with selective unfolding\n" uu____7839))));
(

let uu____7840 = (

let uu____7849 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_only) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____7869 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left yesno uu____7869))
end)
in (

let uu____7876 = (

let uu____7885 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_attr) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____7905 = (FStar_Util.for_some (fun at -> (FStar_Util.for_some (fun lid -> (FStar_Syntax_Util.is_fvar lid at)) lids)) attrs)
in (FStar_All.pipe_left yesno uu____7905))
end)
in (

let uu____7916 = (

let uu____7925 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_fully) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____7945 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left fullyno uu____7945))
end)
in (uu____7925)::[])
in (uu____7885)::uu____7916))
in (uu____7849)::uu____7876))
in (comb_or uu____7840));
)
end
| (uu____7976, uu____7977, uu____7978, FStar_Pervasives_Native.Some (uu____7979)) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8047 -> (

let uu____8048 = (FStar_Syntax_Print.fv_to_string fv)
in (FStar_Util.print1 "should_unfold: Reached a %s with selective unfolding\n" uu____8048))));
(

let uu____8049 = (

let uu____8058 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_only) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8078 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left yesno uu____8078))
end)
in (

let uu____8085 = (

let uu____8094 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_attr) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8114 = (FStar_Util.for_some (fun at -> (FStar_Util.for_some (fun lid -> (FStar_Syntax_Util.is_fvar lid at)) lids)) attrs)
in (FStar_All.pipe_left yesno uu____8114))
end)
in (

let uu____8125 = (

let uu____8134 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_fully) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8154 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left fullyno uu____8154))
end)
in (uu____8134)::[])
in (uu____8094)::uu____8125))
in (uu____8058)::uu____8085))
in (comb_or uu____8049));
)
end
| uu____8185 -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8231 -> (

let uu____8232 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____8233 = (FStar_Syntax_Print.delta_depth_to_string fv.FStar_Syntax_Syntax.fv_delta)
in (

let uu____8234 = (FStar_Common.string_of_list FStar_TypeChecker_Env.string_of_delta_level cfg.FStar_TypeChecker_Cfg.delta_level)
in (FStar_Util.print3 "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n" uu____8232 uu____8233 uu____8234))))));
(

let uu____8235 = (FStar_All.pipe_right cfg.FStar_TypeChecker_Cfg.delta_level (FStar_Util.for_some (fun uu___271_8239 -> (match (uu___271_8239) with
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

let uu____8241 = (FStar_TypeChecker_Env.delta_depth_of_fv cfg.FStar_TypeChecker_Cfg.tcenv fv)
in (FStar_TypeChecker_Common.delta_depth_greater_than uu____8241 l))
end))))
in (FStar_All.pipe_left yesno uu____8235));
)
end)
end
end
in ((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8253 -> (

let uu____8254 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____8255 = (

let uu____8256 = (FStar_Syntax_Syntax.range_of_fv fv)
in (FStar_Range.string_of_range uu____8256))
in (

let uu____8257 = (string_of_res res)
in (FStar_Util.print3 "should_unfold: For %s (%s), unfolding res = %s\n" uu____8254 uu____8255 uu____8257))))));
(match (res) with
| (false, uu____8258, uu____8259) -> begin
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
| uu____8260 -> begin
(

let uu____8267 = (

let uu____8268 = (string_of_res res)
in (FStar_Util.format1 "Unexpected unfolding result: %s" uu____8268))
in (FStar_All.pipe_left failwith uu____8267))
end);
))))))))))))


let decide_unfolding : 'Auu____8283 . FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack_elt Prims.list  ->  'Auu____8283  ->  FStar_Syntax_Syntax.fv  ->  FStar_TypeChecker_Env.qninfo  ->  (FStar_TypeChecker_Cfg.cfg * stack_elt Prims.list) FStar_Pervasives_Native.option = (fun cfg env stack rng fv qninfo -> (

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

let uu___304_8352 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___305_8355 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___305_8355.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___305_8355.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___305_8355.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___305_8355.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___305_8355.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___305_8355.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___305_8355.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant); FStar_TypeChecker_Cfg.unfold_only = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_fully = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_attr = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_tac = uu___305_8355.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___305_8355.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___305_8355.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___305_8355.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___305_8355.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___305_8355.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___305_8355.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___305_8355.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___305_8355.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___305_8355.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___305_8355.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___305_8355.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___305_8355.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___305_8355.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___305_8355.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___304_8352.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___304_8352.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___304_8352.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___304_8352.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___304_8352.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___304_8352.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___304_8352.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___304_8352.FStar_TypeChecker_Cfg.reifying})
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

let uu____8417 = (push1 e t)
in (UnivArgs (((us), (r))))::uu____8417)
end
| (h)::t -> begin
(e)::(h)::t
end))
in (

let ref = (

let uu____8429 = (

let uu____8436 = (

let uu____8437 = (

let uu____8438 = (FStar_Syntax_Syntax.lid_of_fv fv)
in FStar_Const.Const_reflect (uu____8438))
in FStar_Syntax_Syntax.Tm_constant (uu____8437))
in (FStar_Syntax_Syntax.mk uu____8436))
in (uu____8429 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let stack1 = (push1 (App (((env), (ref), (FStar_Pervasives_Native.None), (FStar_Range.dummyRange)))) stack)
in FStar_Pervasives_Native.Some (((cfg), (stack1))))))
end)))


let is_fext_on_domain : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let fext_lid = (fun s -> (FStar_Ident.lid_of_path (("FStar")::("FunctionalExtensionality")::(s)::[]) FStar_Range.dummyRange))
in (

let on_domain_lids = (FStar_All.pipe_right (("on_domain")::("on_dom")::("on_domain_g")::("on_dom_g")::[]) (FStar_List.map fext_lid))
in (

let is_on_dom = (fun fv -> (FStar_All.pipe_right on_domain_lids (FStar_List.existsb (fun l -> (FStar_Syntax_Syntax.fv_eq_lid fv l)))))
in (

let uu____8485 = (

let uu____8486 = (FStar_Syntax_Subst.compress t)
in uu____8486.FStar_Syntax_Syntax.n)
in (match (uu____8485) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____8517 = (

let uu____8518 = (FStar_Syntax_Util.un_uinst hd1)
in uu____8518.FStar_Syntax_Syntax.n)
in (match (uu____8517) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((is_on_dom fv) && (Prims.op_Equality (FStar_List.length args) (Prims.parse_int "3"))) -> begin
(

let f = (

let uu____8533 = (

let uu____8540 = (

let uu____8551 = (FStar_All.pipe_right args FStar_List.tl)
in (FStar_All.pipe_right uu____8551 FStar_List.tl))
in (FStar_All.pipe_right uu____8540 FStar_List.hd))
in (FStar_All.pipe_right uu____8533 FStar_Pervasives_Native.fst))
in FStar_Pervasives_Native.Some (f))
end
| uu____8650 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____8651 -> begin
FStar_Pervasives_Native.None
end))))))


let rec norm : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t1 = ((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.norm_delayed) with
| true -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____8928) -> begin
(

let uu____8951 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "NORM delayed: %s\n" uu____8951))
end
| uu____8952 -> begin
()
end)
end
| uu____8953 -> begin
()
end);
(FStar_Syntax_Subst.compress t);
)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____8961 -> (

let uu____8962 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____8963 = (FStar_Util.string_of_bool cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.no_full_norm)
in (

let uu____8964 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____8965 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____8972 = (

let uu____8973 = (

let uu____8976 = (firstn (Prims.parse_int "4") stack)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8976))
in (stack_to_string uu____8973))
in (FStar_Util.print5 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n" uu____8962 uu____8963 uu____8964 uu____8965 uu____8972))))))));
(FStar_TypeChecker_Cfg.log_cfg cfg (fun uu____9002 -> (

let uu____9003 = (FStar_TypeChecker_Cfg.cfg_to_string cfg)
in (FStar_Util.print1 ">>> cfg = %s\n" uu____9003))));
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9007 -> (

let uu____9008 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9008))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_constant (uu____9009) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9013 -> (

let uu____9014 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9014))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_name (uu____9015) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9019 -> (

let uu____9020 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9020))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_lazy (uu____9021) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9025 -> (

let uu____9026 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9026))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____9027; FStar_Syntax_Syntax.fv_delta = uu____9028; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9032 -> (

let uu____9033 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9033))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____9034; FStar_Syntax_Syntax.fv_delta = uu____9035; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____9036))}) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9046 -> (

let uu____9047 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9047))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let qninfo = (FStar_TypeChecker_Env.lookup_qname cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (

let uu____9051 = (FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo)
in (match (uu____9051) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level (_0_2)) when (_0_2 = (Prims.parse_int "0")) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9057 -> (

let uu____9058 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9058))));
(rebuild cfg env stack t1);
)
end
| uu____9059 -> begin
(

let uu____9062 = (decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv qninfo)
in (match (uu____9062) with
| FStar_Pervasives_Native.Some (cfg1, stack1) -> begin
(do_unfold_fv cfg1 env stack1 t1 qninfo fv)
end
| FStar_Pervasives_Native.None -> begin
(rebuild cfg env stack t1)
end))
end))))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____9089) -> begin
(

let uu____9096 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____9096))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____9098; FStar_Syntax_Syntax.vars = uu____9099}, (uu____9100)::[]) when (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.assert_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.assert_norm_lid)) && cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.for_extraction) -> begin
(norm cfg env stack FStar_Syntax_Util.exp_unit)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____9140; FStar_Syntax_Syntax.vars = uu____9141}, uu____9142); FStar_Syntax_Syntax.pos = uu____9143; FStar_Syntax_Syntax.vars = uu____9144}, (uu____9145)::[]) when (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.assert_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.assert_norm_lid)) && cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.for_extraction) -> begin
(norm cfg env stack FStar_Syntax_Util.exp_unit)
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when ((should_consider_norm_requests cfg) && (

let uu____9215 = (is_norm_request hd1 args)
in (Prims.op_Equality uu____9215 Norm_request_requires_rejig))) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(FStar_Util.print_string "Rejigging norm request ... \n")
end
| uu____9217 -> begin
()
end);
(

let uu____9218 = (rejig_norm_request hd1 args)
in (norm cfg env stack uu____9218));
)
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when ((should_consider_norm_requests cfg) && (

let uu____9246 = (is_norm_request hd1 args)
in (Prims.op_Equality uu____9246 Norm_request_ready))) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(FStar_Util.print_string "Potential norm request ... \n")
end
| uu____9248 -> begin
()
end);
(

let cfg' = (

let uu___306_9250 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___307_9253 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___307_9253.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___307_9253.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___307_9253.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___307_9253.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___307_9253.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___307_9253.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = false; FStar_TypeChecker_Cfg.unfold_until = uu___307_9253.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_fully = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_attr = uu___307_9253.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___307_9253.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___307_9253.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___307_9253.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___307_9253.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___307_9253.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___307_9253.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___307_9253.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___307_9253.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___307_9253.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___307_9253.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___307_9253.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___307_9253.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___307_9253.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___307_9253.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___307_9253.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___306_9250.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___306_9250.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]; FStar_TypeChecker_Cfg.primitive_steps = uu___306_9250.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___306_9250.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___306_9250.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = true; FStar_TypeChecker_Cfg.reifying = uu___306_9250.FStar_TypeChecker_Cfg.reifying})
in (

let uu____9258 = (get_norm_request cfg (norm cfg' env []) args)
in (match (uu____9258) with
| FStar_Pervasives_Native.None -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(FStar_Util.print_string "Norm request None ... \n")
end
| uu____9276 -> begin
()
end);
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____9291 stack1 -> (match (uu____9291) with
| (a, aq) -> begin
(

let uu____9303 = (

let uu____9304 = (

let uu____9311 = (

let uu____9312 = (

let uu____9343 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____9343), (false)))
in Clos (uu____9312))
in ((uu____9311), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____9304))
in (uu____9303)::stack1)
end)) args))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____9431 -> (

let uu____9432 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____9432))));
(norm cfg env stack1 hd1);
));
)
end
| FStar_Pervasives_Native.Some (s, tm) when (is_nbe_request s) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(

let uu____9454 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Starting NBE request on %s ... \n" uu____9454))
end
| uu____9455 -> begin
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

let uu____9461 = (

let uu____9462 = (

let uu____9463 = (FStar_Util.time_diff start fin)
in (FStar_Pervasives_Native.snd uu____9463))
in (FStar_Util.string_of_int uu____9462))
in (

let uu____9468 = (FStar_Syntax_Print.term_to_string tm')
in (

let uu____9469 = (FStar_Syntax_Print.term_to_string tm_norm)
in (FStar_Util.print3 "NBE\'d (%s ms) %s\n\tto %s\n" uu____9461 uu____9468 uu____9469))))
end
| uu____9470 -> begin
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

let uu____9484 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Starting norm request on %s ... \n" uu____9484))
end
| uu____9485 -> begin
()
end);
(

let delta_level = (

let uu____9489 = (FStar_All.pipe_right s (FStar_Util.for_some (fun uu___272_9494 -> (match (uu___272_9494) with
| FStar_TypeChecker_Env.UnfoldUntil (uu____9495) -> begin
true
end
| FStar_TypeChecker_Env.UnfoldOnly (uu____9496) -> begin
true
end
| FStar_TypeChecker_Env.UnfoldFully (uu____9499) -> begin
true
end
| uu____9502 -> begin
false
end))))
in (match (uu____9489) with
| true -> begin
(FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]
end
| uu____9505 -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end))
in (

let cfg'1 = (

let uu___308_9507 = cfg
in (

let uu____9508 = (

let uu___309_9509 = (FStar_TypeChecker_Cfg.to_fsteps s)
in {FStar_TypeChecker_Cfg.beta = uu___309_9509.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___309_9509.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___309_9509.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___309_9509.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___309_9509.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___309_9509.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___309_9509.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___309_9509.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___309_9509.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___309_9509.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___309_9509.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___309_9509.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___309_9509.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___309_9509.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___309_9509.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___309_9509.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___309_9509.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___309_9509.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___309_9509.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___309_9509.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___309_9509.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___309_9509.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = true; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___309_9509.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___309_9509.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___309_9509.FStar_TypeChecker_Cfg.for_extraction})
in {FStar_TypeChecker_Cfg.steps = uu____9508; FStar_TypeChecker_Cfg.tcenv = uu___308_9507.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___308_9507.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___308_9507.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___308_9507.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___308_9507.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = true; FStar_TypeChecker_Cfg.reifying = uu___308_9507.FStar_TypeChecker_Cfg.reifying}))
in (

let stack' = (

let tail1 = (Cfg (cfg))::stack
in (match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(

let uu____9514 = (

let uu____9515 = (

let uu____9520 = (FStar_Util.now ())
in ((t1), (uu____9520)))
in Debug (uu____9515))
in (uu____9514)::tail1)
end
| uu____9521 -> begin
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

let uu____9524 = (mk (FStar_Syntax_Syntax.Tm_type (u1)) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack uu____9524)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.erase_universes) with
| true -> begin
(norm cfg env stack t')
end
| uu____9531 -> begin
(

let us1 = (

let uu____9533 = (

let uu____9540 = (FStar_List.map (norm_universe cfg env) us)
in ((uu____9540), (t1.FStar_Syntax_Syntax.pos)))
in UnivArgs (uu____9533))
in (

let stack1 = (us1)::stack
in (norm cfg env stack1 t')))
end)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____9549 = (lookup_bvar env x)
in (match (uu____9549) with
| Univ (uu____9550) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env1, t0, r, fix) -> begin
(match (((not (fix)) || cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta)) with
| true -> begin
(

let uu____9599 = (FStar_ST.op_Bang r)
in (match (uu____9599) with
| FStar_Pervasives_Native.Some (env2, t') -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____9717 -> (

let uu____9718 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____9719 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" uu____9718 uu____9719)))));
(

let uu____9720 = (maybe_weakly_reduced t')
in (match (uu____9720) with
| true -> begin
(match (stack) with
| [] when (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak || cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars) -> begin
(rebuild cfg env2 stack t')
end
| uu____9721 -> begin
(norm cfg env2 stack t')
end)
end
| uu____9722 -> begin
(rebuild cfg env2 stack t')
end));
)
end
| FStar_Pervasives_Native.None -> begin
(norm cfg env1 ((MemoLazy (r))::stack) t0)
end))
end
| uu____9768 -> begin
(norm cfg env1 stack t0)
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack) with
| (UnivArgs (uu____9796))::uu____9797 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Arg (c, uu____9807, uu____9808))::stack_rest -> begin
(match (c) with
| Univ (uu____9812) -> begin
(norm cfg ((((FStar_Pervasives_Native.None), (c)))::env) stack_rest t1)
end
| uu____9821 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (b)::[] -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____9850 -> (

let uu____9851 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____9851))));
(norm cfg ((((FStar_Pervasives_Native.Some (b)), (c)))::env) stack_rest body);
)
end
| (b)::tl1 -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____9885 -> (

let uu____9886 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____9886))));
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
(FStar_TypeChecker_Cfg.log cfg (fun uu____9954 -> (

let uu____9955 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____9955))));
(norm cfg env stack1 t1);
)
end
| (Match (uu____9956))::uu____9957 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____9969 -> begin
(

let uu____9970 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____9970) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____10006 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____10049 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____10049))))
end
| uu____10050 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___310_10056 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___310_10056.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___310_10056.FStar_Syntax_Syntax.residual_flags})))
end
| uu____10057 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10063 -> (

let uu____10064 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____10064))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___311_10075 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___311_10075.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___311_10075.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___311_10075.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___311_10075.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___311_10075.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___311_10075.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___311_10075.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___311_10075.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Debug (uu____10078))::uu____10079 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____10087 -> begin
(

let uu____10088 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____10088) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____10124 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____10167 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____10167))))
end
| uu____10168 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___310_10174 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___310_10174.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___310_10174.FStar_Syntax_Syntax.residual_flags})))
end
| uu____10175 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10181 -> (

let uu____10182 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____10182))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___311_10193 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___311_10193.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___311_10193.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___311_10193.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___311_10193.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___311_10193.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___311_10193.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___311_10193.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___311_10193.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Meta (uu____10196))::uu____10197 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____10207 -> begin
(

let uu____10208 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____10208) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____10244 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____10287 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____10287))))
end
| uu____10288 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___310_10294 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___310_10294.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___310_10294.FStar_Syntax_Syntax.residual_flags})))
end
| uu____10295 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10301 -> (

let uu____10302 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____10302))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___311_10313 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___311_10313.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___311_10313.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___311_10313.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___311_10313.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___311_10313.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___311_10313.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___311_10313.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___311_10313.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Let (uu____10316))::uu____10317 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____10329 -> begin
(

let uu____10330 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____10330) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____10366 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____10409 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____10409))))
end
| uu____10410 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___310_10416 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___310_10416.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___310_10416.FStar_Syntax_Syntax.residual_flags})))
end
| uu____10417 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10423 -> (

let uu____10424 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____10424))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___311_10435 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___311_10435.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___311_10435.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___311_10435.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___311_10435.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___311_10435.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___311_10435.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___311_10435.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___311_10435.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (App (uu____10438))::uu____10439 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____10451 -> begin
(

let uu____10452 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____10452) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____10488 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____10531 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____10531))))
end
| uu____10532 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___310_10538 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___310_10538.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___310_10538.FStar_Syntax_Syntax.residual_flags})))
end
| uu____10539 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10545 -> (

let uu____10546 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____10546))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___311_10557 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___311_10557.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___311_10557.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___311_10557.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___311_10557.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___311_10557.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___311_10557.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___311_10557.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___311_10557.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Abs (uu____10560))::uu____10561 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____10577 -> begin
(

let uu____10578 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____10578) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____10614 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____10657 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____10657))))
end
| uu____10658 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___310_10664 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___310_10664.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___310_10664.FStar_Syntax_Syntax.residual_flags})))
end
| uu____10665 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10671 -> (

let uu____10672 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____10672))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___311_10683 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___311_10683.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___311_10683.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___311_10683.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___311_10683.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___311_10683.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___311_10683.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___311_10683.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___311_10683.FStar_TypeChecker_Cfg.reifying})
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
| uu____10687 -> begin
(

let uu____10688 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____10688) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____10724 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____10767 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____10767))))
end
| uu____10768 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___310_10774 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___310_10774.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___310_10774.FStar_Syntax_Syntax.residual_flags})))
end
| uu____10775 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10781 -> (

let uu____10782 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____10782))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___311_10793 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___311_10793.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___311_10793.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___311_10793.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___311_10793.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___311_10793.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___311_10793.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___311_10793.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___311_10793.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____10836 stack1 -> (match (uu____10836) with
| (a, aq) -> begin
(

let uu____10848 = (

let uu____10849 = (

let uu____10856 = (

let uu____10857 = (

let uu____10888 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____10888), (false)))
in Clos (uu____10857))
in ((uu____10856), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____10849))
in (uu____10848)::stack1)
end)) args))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10976 -> (

let uu____10977 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____10977))));
(norm cfg env stack1 head1);
))
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

let uu___312_11025 = x
in {FStar_Syntax_Syntax.ppname = uu___312_11025.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___312_11025.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t2)))
end
| uu____11026 -> begin
(

let uu____11041 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____11041))
end)
end
| uu____11042 -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let uu____11044 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____11044) with
| (closing, f1) -> begin
(

let f2 = (norm cfg ((dummy)::env) [] f1)
in (

let t2 = (

let uu____11075 = (

let uu____11076 = (

let uu____11083 = (FStar_Syntax_Subst.close closing f2)
in (((

let uu___313_11089 = x
in {FStar_Syntax_Syntax.ppname = uu___313_11089.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___313_11089.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (uu____11083)))
in FStar_Syntax_Syntax.Tm_refine (uu____11076))
in (mk uu____11075 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t2)))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let uu____11112 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____11112))
end
| uu____11113 -> begin
(

let uu____11114 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____11114) with
| (bs1, c1) -> begin
(

let c2 = (

let uu____11122 = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11148 -> (dummy)::env1) env))
in (norm_comp cfg uu____11122 c1))
in (

let t2 = (

let uu____11172 = (norm_binders cfg env bs1)
in (FStar_Syntax_Util.arrow uu____11172 c2))
in (rebuild cfg env stack t2)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unascribe -> begin
(norm cfg env stack t11)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) -> begin
(match (stack) with
| (Match (uu____11285))::uu____11286 when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.beta -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____11299 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (Arg (uu____11300))::uu____11301 when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.beta -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____11312 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (App (uu____11313, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____11314; FStar_Syntax_Syntax.vars = uu____11315}, uu____11316, uu____11317))::uu____11318 when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.beta -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____11325 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (MemoLazy (uu____11326))::uu____11327 when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.beta -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____11338 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| uu____11339 -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____11342 -> (FStar_Util.print_string "+++ Keeping ascription \n")));
(

let t12 = (norm cfg env [] t11)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11346 -> (FStar_Util.print_string "+++ Normalizing ascription \n")));
(

let tc1 = (match (tc) with
| FStar_Util.Inl (t2) -> begin
(

let uu____11371 = (norm cfg env [] t2)
in FStar_Util.Inl (uu____11371))
end
| FStar_Util.Inr (c) -> begin
(

let uu____11385 = (norm_comp cfg env c)
in FStar_Util.Inr (uu____11385))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (norm cfg env []))
in (match (stack) with
| (Cfg (cfg1))::stack1 -> begin
(

let t2 = (

let uu____11408 = (

let uu____11409 = (

let uu____11436 = (FStar_Syntax_Util.unascribe t12)
in ((uu____11436), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____11409))
in (mk uu____11408 t1.FStar_Syntax_Syntax.pos))
in (norm cfg1 env stack1 t2))
end
| uu____11471 -> begin
(

let uu____11472 = (

let uu____11473 = (

let uu____11474 = (

let uu____11501 = (FStar_Syntax_Util.unascribe t12)
in ((uu____11501), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____11474))
in (mk uu____11473 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack uu____11472))
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

let uu___314_11578 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___315_11581 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___315_11581.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___315_11581.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___315_11581.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = true; FStar_TypeChecker_Cfg.hnf = uu___315_11581.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___315_11581.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___315_11581.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___315_11581.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___315_11581.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___315_11581.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___315_11581.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___315_11581.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___315_11581.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___315_11581.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___315_11581.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___315_11581.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___315_11581.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___315_11581.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___315_11581.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___315_11581.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___315_11581.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___315_11581.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___315_11581.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___315_11581.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___315_11581.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___315_11581.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___314_11578.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___314_11578.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___314_11578.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___314_11578.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___314_11578.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___314_11578.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___314_11578.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___314_11578.FStar_TypeChecker_Cfg.reifying})
in (norm cfg' env ((Cfg (cfg))::stack1) head1))
end
| uu____11582 -> begin
(norm cfg env stack1 head1)
end))
end
| FStar_Syntax_Syntax.Tm_let ((b, lbs), lbody) when ((FStar_Syntax_Syntax.is_top_level lbs) && cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____11617 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____11617) with
| (openings, lbunivs) -> begin
(

let cfg1 = (

let uu___316_11637 = cfg
in (

let uu____11638 = (FStar_TypeChecker_Env.push_univ_vars cfg.FStar_TypeChecker_Cfg.tcenv lbunivs)
in {FStar_TypeChecker_Cfg.steps = uu___316_11637.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu____11638; FStar_TypeChecker_Cfg.debug = uu___316_11637.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___316_11637.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___316_11637.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___316_11637.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___316_11637.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___316_11637.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___316_11637.FStar_TypeChecker_Cfg.reifying}))
in (

let norm1 = (fun t2 -> (

let uu____11645 = (

let uu____11646 = (FStar_Syntax_Subst.subst openings t2)
in (norm cfg1 env [] uu____11646))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____11645)))
in (

let lbtyp = (norm1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (norm1 lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___317_11649 = lb
in {FStar_Syntax_Syntax.lbname = uu___317_11649.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___317_11649.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___317_11649.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___317_11649.FStar_Syntax_Syntax.lbpos})))))
end)))))
in (

let uu____11650 = (mk (FStar_Syntax_Syntax.Tm_let (((((b), (lbs1))), (lbody)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack uu____11650)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____11661, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____11662); FStar_Syntax_Syntax.lbunivs = uu____11663; FStar_Syntax_Syntax.lbtyp = uu____11664; FStar_Syntax_Syntax.lbeff = uu____11665; FStar_Syntax_Syntax.lbdef = uu____11666; FStar_Syntax_Syntax.lbattrs = uu____11667; FStar_Syntax_Syntax.lbpos = uu____11668})::uu____11669), uu____11670) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n1 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in (

let uu____11710 = ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets)) && (((cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.pure_subterms_within_computations && (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs FStar_Parser_Const.inline_let_attr)) || ((FStar_Syntax_Util.is_pure_effect n1) && (cfg.FStar_TypeChecker_Cfg.normalize_pure_lets || (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs FStar_Parser_Const.inline_let_attr)))) || ((FStar_Syntax_Util.is_ghost_effect n1) && (not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.pure_subterms_within_computations)))))
in (match (uu____11710) with
| true -> begin
(

let binder = (

let uu____11712 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____11712))
in (

let env1 = (

let uu____11722 = (

let uu____11729 = (

let uu____11730 = (

let uu____11761 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (uu____11761), (false)))
in Clos (uu____11730))
in ((FStar_Pervasives_Native.Some (binder)), (uu____11729)))
in (uu____11722)::env)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11856 -> (FStar_Util.print_string "+++ Reducing Tm_let\n")));
(norm cfg env1 stack body);
)))
end
| uu____11857 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____11860 -> (FStar_Util.print_string "+++ Not touching Tm_let\n")));
(

let uu____11861 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____11861));
)
end
| uu____11862 -> begin
(

let uu____11863 = (

let uu____11868 = (

let uu____11869 = (

let uu____11876 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right uu____11876 FStar_Syntax_Syntax.mk_binder))
in (uu____11869)::[])
in (FStar_Syntax_Subst.open_term uu____11868 body))
in (match (uu____11863) with
| (bs, body1) -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____11903 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- type")));
(

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let x = (

let uu____11911 = (FStar_List.hd bs)
in (FStar_Pervasives_Native.fst uu____11911))
in FStar_Util.Inl ((

let uu___318_11927 = x
in {FStar_Syntax_Syntax.ppname = uu___318_11927.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___318_11927.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11930 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- definiens\n")));
(

let lb1 = (

let uu___319_11932 = lb
in (

let uu____11933 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___319_11932.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___319_11932.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____11933; FStar_Syntax_Syntax.lbattrs = uu___319_11932.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___319_11932.FStar_Syntax_Syntax.lbpos}))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env1 uu____11962 -> (dummy)::env1) env))
in (

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___320_11987 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___320_11987.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___320_11987.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___320_11987.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___320_11987.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___320_11987.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___320_11987.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___320_11987.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___320_11987.FStar_TypeChecker_Cfg.reifying})
in ((FStar_TypeChecker_Cfg.log cfg1 (fun uu____11990 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- body\n")));
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

let uu____12007 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____12007) with
| (lbs1, body1) -> begin
(

let lbs2 = (FStar_List.map (fun lb -> (

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let uu____12043 = (

let uu___321_12044 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___321_12044.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___321_12044.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})
in FStar_Util.Inl (uu____12043))
in (

let uu____12045 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____12045) with
| (xs, def_body, lopt) -> begin
(

let xs1 = (norm_binders cfg env xs)
in (

let env1 = (

let uu____12071 = (FStar_List.map (fun uu____12087 -> dummy) lbs1)
in (

let uu____12088 = (

let uu____12097 = (FStar_List.map (fun uu____12119 -> dummy) xs1)
in (FStar_List.append uu____12097 env))
in (FStar_List.append uu____12071 uu____12088)))
in (

let def_body1 = (norm cfg env1 [] def_body)
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____12145 = (

let uu___322_12146 = rc
in (

let uu____12147 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env1 []))
in {FStar_Syntax_Syntax.residual_effect = uu___322_12146.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____12147; FStar_Syntax_Syntax.residual_flags = uu___322_12146.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____12145))
end
| uu____12156 -> begin
lopt
end)
in (

let def = (FStar_Syntax_Util.abs xs1 def_body1 lopt1)
in (

let uu___323_12162 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___323_12162.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___323_12162.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___323_12162.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___323_12162.FStar_Syntax_Syntax.lbpos}))))))
end))))) lbs1)
in (

let env' = (

let uu____12172 = (FStar_List.map (fun uu____12188 -> dummy) lbs2)
in (FStar_List.append uu____12172 env))
in (

let body2 = (norm cfg env' [] body1)
in (

let uu____12196 = (FStar_Syntax_Subst.close_let_rec lbs2 body2)
in (match (uu____12196) with
| (lbs3, body3) -> begin
(

let t2 = (

let uu___324_12212 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (body3))); FStar_Syntax_Syntax.pos = uu___324_12212.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___324_12212.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack t2))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta)) -> begin
(

let uu____12241 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____12241))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let uu____12260 = (FStar_List.fold_right (fun lb uu____12336 -> (match (uu____12336) with
| (rec_env, memos, i) -> begin
(

let bv = (

let uu___325_12457 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___325_12457.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___325_12457.FStar_Syntax_Syntax.sort})
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
in (match (uu____12260) with
| (rec_env, memos, uu____12684) -> begin
(

let uu____12737 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (FStar_Pervasives_Native.Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (FStar_Pervasives_Native.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env1 -> (

let uu____13048 = (

let uu____13055 = (

let uu____13056 = (

let uu____13087 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (uu____13087), (false)))
in Clos (uu____13056))
in ((FStar_Pervasives_Native.None), (uu____13055)))
in (uu____13048)::env1)) (FStar_Pervasives_Native.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head1, m) -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____13191 -> (

let uu____13192 = (FStar_Syntax_Print.metadata_to_string m)
in (FStar_Util.print1 ">> metadata = %s\n" uu____13192))));
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m1, t2) -> begin
(reduce_impure_comp cfg env stack head1 (FStar_Util.Inl (m1)) t2)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) -> begin
(reduce_impure_comp cfg env stack head1 (FStar_Util.Inr (((m1), (m')))) t2)
end
| uu____13214 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unmeta) with
| true -> begin
(norm cfg env stack head1)
end
| uu____13215 -> begin
(match (stack) with
| (uu____13216)::uu____13217 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____13222) -> begin
(norm cfg env ((Meta (((env), (m), (r))))::stack) head1)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args1 = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((env), (FStar_Syntax_Syntax.Meta_pattern (args1)), (t1.FStar_Syntax_Syntax.pos))))::stack) head1))
end
| uu____13249 -> begin
(norm cfg env stack head1)
end)
end
| [] -> begin
(

let head2 = (norm cfg env [] head1)
in (

let m1 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let uu____13265 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (uu____13265))
end
| uu____13278 -> begin
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
| FStar_Syntax_Syntax.Tm_delayed (uu____13284) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (norm cfg env stack t2))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____13308) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____13322) -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(

let uu____13335 = (

let uu____13336 = (FStar_Range.string_of_range t2.FStar_Syntax_Syntax.pos)
in (

let uu____13337 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "(%s) CheckNoUvars: Unexpected unification variable remains: %s" uu____13336 uu____13337)))
in (failwith uu____13335))
end
| uu____13338 -> begin
(

let uu____13339 = (inline_closure_env cfg env [] t2)
in (rebuild cfg env stack uu____13339))
end)
end
| uu____13340 -> begin
(norm cfg env stack t2)
end))
end);
)))
and do_unfold_fv : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.qninfo  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t0 qninfo f -> (

let uu____13349 = (FStar_TypeChecker_Env.lookup_definition_qninfo cfg.FStar_TypeChecker_Cfg.delta_level f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v qninfo)
in (match (uu____13349) with
| FStar_Pervasives_Native.None -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____13363 -> (

let uu____13364 = (FStar_Syntax_Print.fv_to_string f)
in (FStar_Util.print1 " >> Tm_fvar case 2 for %s\n" uu____13364))));
(rebuild cfg env stack t0);
)
end
| FStar_Pervasives_Native.Some (us, t) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____13375 -> (

let uu____13376 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____13377 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 " >> Unfolded %s to %s\n" uu____13376 uu____13377)))));
(

let t1 = (match ((Prims.op_Equality cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_until (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)))) with
| true -> begin
t
end
| uu____13381 -> begin
(FStar_Syntax_Subst.set_use_range t0.FStar_Syntax_Syntax.pos t)
end)
in (

let n1 = (FStar_List.length us)
in (match ((n1 > (Prims.parse_int "0"))) with
| true -> begin
(match (stack) with
| (UnivArgs (us', uu____13390))::stack1 -> begin
((

let uu____13399 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv) (FStar_Options.Other ("univ_norm")))
in (match (uu____13399) with
| true -> begin
(FStar_List.iter (fun x -> (

let uu____13403 = (FStar_Syntax_Print.univ_to_string x)
in (FStar_Util.print1 "Univ (normalizer) %s\n" uu____13403))) us')
end
| uu____13404 -> begin
()
end));
(

let env1 = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env1 u -> (((FStar_Pervasives_Native.None), (Univ (u))))::env1) env))
in (norm cfg env1 stack1 t1));
)
end
| uu____13436 when (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.erase_universes || cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.allow_unbound_universes) -> begin
(norm cfg env stack t1)
end
| uu____13439 -> begin
(

let uu____13442 = (

let uu____13443 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" uu____13443))
in (failwith uu____13442))
end)
end
| uu____13444 -> begin
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

let uu___326_13467 = cfg
in (

let uu____13468 = (FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one new_steps cfg.FStar_TypeChecker_Cfg.steps)
in {FStar_TypeChecker_Cfg.steps = uu____13468; FStar_TypeChecker_Cfg.tcenv = uu___326_13467.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___326_13467.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = (FStar_TypeChecker_Env.InliningDelta)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; FStar_TypeChecker_Cfg.primitive_steps = uu___326_13467.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___326_13467.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___326_13467.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___326_13467.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___326_13467.FStar_TypeChecker_Cfg.reifying})))
end
| uu____13469 -> begin
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
| (App (uu____13498, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____13499; FStar_Syntax_Syntax.vars = uu____13500}, uu____13501, uu____13502))::uu____13503 -> begin
()
end
| uu____13508 -> begin
(

let uu____13511 = (

let uu____13512 = (stack_to_string stack)
in (FStar_Util.format1 "INTERNAL ERROR: do_reify_monadic: bad stack: %s" uu____13512))
in (failwith uu____13511))
end);
(

let head0 = head1
in (

let head2 = (FStar_Syntax_Util.unascribe head1)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____13519 -> (

let uu____13520 = (FStar_Syntax_Print.tag_of_term head2)
in (

let uu____13521 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print2 "Reifying: (%s) %s\n" uu____13520 uu____13521)))));
(

let head3 = (FStar_Syntax_Util.unmeta_safe head2)
in (

let uu____13523 = (

let uu____13524 = (FStar_Syntax_Subst.compress head3)
in uu____13524.FStar_Syntax_Syntax.n)
in (match (uu____13523) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (

let uu____13542 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv m)
in (FStar_TypeChecker_Env.get_effect_decl cfg.FStar_TypeChecker_Cfg.tcenv uu____13542))
in (

let uu____13543 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____13543) with
| (uu____13544, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____13554) -> begin
(failwith "Cannot reify a top-level let binding")
end
| FStar_Util.Inl (x) -> begin
(

let is_return = (fun e -> (

let uu____13564 = (

let uu____13565 = (FStar_Syntax_Subst.compress e)
in uu____13565.FStar_Syntax_Syntax.n)
in (match (uu____13564) with
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____13571, uu____13572)) -> begin
(

let uu____13581 = (

let uu____13582 = (FStar_Syntax_Subst.compress e1)
in uu____13582.FStar_Syntax_Syntax.n)
in (match (uu____13581) with
| FStar_Syntax_Syntax.Tm_meta (e2, FStar_Syntax_Syntax.Meta_monadic_lift (uu____13588, msrc, uu____13590)) when (FStar_Syntax_Util.is_pure_effect msrc) -> begin
(

let uu____13599 = (FStar_Syntax_Subst.compress e2)
in FStar_Pervasives_Native.Some (uu____13599))
end
| uu____13600 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____13601 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____13602 = (is_return lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____13602) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let lb1 = (

let uu___327_13607 = lb
in {FStar_Syntax_Syntax.lbname = uu___327_13607.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___327_13607.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___327_13607.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu___327_13607.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___327_13607.FStar_Syntax_Syntax.lbpos})
in (

let uu____13608 = (FStar_List.tl stack)
in (

let uu____13609 = (

let uu____13610 = (

let uu____13617 = (

let uu____13618 = (

let uu____13631 = (FStar_Syntax_Util.mk_reify body)
in ((((false), ((lb1)::[]))), (uu____13631)))
in FStar_Syntax_Syntax.Tm_let (uu____13618))
in (FStar_Syntax_Syntax.mk uu____13617))
in (uu____13610 FStar_Pervasives_Native.None head3.FStar_Syntax_Syntax.pos))
in (norm cfg env uu____13608 uu____13609))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____13647 = (

let uu____13648 = (is_return body)
in (match (uu____13648) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_bvar (y); FStar_Syntax_Syntax.pos = uu____13652; FStar_Syntax_Syntax.vars = uu____13653}) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____13656 -> begin
false
end))
in (match (uu____13647) with
| true -> begin
(norm cfg env stack lb.FStar_Syntax_Syntax.lbdef)
end
| uu____13659 -> begin
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

let uu____13677 = (

let uu____13684 = (

let uu____13685 = (

let uu____13704 = (

let uu____13713 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____13713)::[])
in ((uu____13704), (body1), (FStar_Pervasives_Native.Some (body_rc))))
in FStar_Syntax_Syntax.Tm_abs (uu____13685))
in (FStar_Syntax_Syntax.mk uu____13684))
in (uu____13677 FStar_Pervasives_Native.None body1.FStar_Syntax_Syntax.pos))
in (

let close1 = (closure_as_term cfg env)
in (

let bind_inst = (

let uu____13755 = (

let uu____13756 = (FStar_Syntax_Subst.compress bind_repr)
in uu____13756.FStar_Syntax_Syntax.n)
in (match (uu____13755) with
| FStar_Syntax_Syntax.Tm_uinst (bind1, (uu____13762)::(uu____13763)::[]) -> begin
(

let uu____13768 = (

let uu____13775 = (

let uu____13776 = (

let uu____13783 = (

let uu____13784 = (

let uu____13785 = (close1 lb.FStar_Syntax_Syntax.lbtyp)
in (cfg.FStar_TypeChecker_Cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.FStar_TypeChecker_Cfg.tcenv uu____13785))
in (

let uu____13786 = (

let uu____13789 = (

let uu____13790 = (close1 t)
in (cfg.FStar_TypeChecker_Cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.FStar_TypeChecker_Cfg.tcenv uu____13790))
in (uu____13789)::[])
in (uu____13784)::uu____13786))
in ((bind1), (uu____13783)))
in FStar_Syntax_Syntax.Tm_uinst (uu____13776))
in (FStar_Syntax_Syntax.mk uu____13775))
in (uu____13768 FStar_Pervasives_Native.None rng))
end
| uu____13796 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let maybe_range_arg = (

let uu____13810 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____13810) with
| true -> begin
(

let uu____13821 = (

let uu____13830 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range lb.FStar_Syntax_Syntax.lbpos lb.FStar_Syntax_Syntax.lbpos)
in (FStar_Syntax_Syntax.as_arg uu____13830))
in (

let uu____13831 = (

let uu____13842 = (

let uu____13851 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range body2.FStar_Syntax_Syntax.pos body2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.as_arg uu____13851))
in (uu____13842)::[])
in (uu____13821)::uu____13831))
end
| uu____13876 -> begin
[]
end))
in (

let reified = (

let uu____13888 = (

let uu____13895 = (

let uu____13896 = (

let uu____13913 = (

let uu____13924 = (

let uu____13935 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____13944 = (

let uu____13955 = (FStar_Syntax_Syntax.as_arg t)
in (uu____13955)::[])
in (uu____13935)::uu____13944))
in (

let uu____13988 = (

let uu____13999 = (

let uu____14010 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____14019 = (

let uu____14030 = (FStar_Syntax_Syntax.as_arg head4)
in (

let uu____14039 = (

let uu____14050 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____14059 = (

let uu____14070 = (FStar_Syntax_Syntax.as_arg body2)
in (uu____14070)::[])
in (uu____14050)::uu____14059))
in (uu____14030)::uu____14039))
in (uu____14010)::uu____14019))
in (FStar_List.append maybe_range_arg uu____13999))
in (FStar_List.append uu____13924 uu____13988)))
in ((bind_inst), (uu____13913)))
in FStar_Syntax_Syntax.Tm_app (uu____13896))
in (FStar_Syntax_Syntax.mk uu____13895))
in (uu____13888 FStar_Pervasives_Native.None rng))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____14154 -> (

let uu____14155 = (FStar_Syntax_Print.term_to_string head0)
in (

let uu____14156 = (FStar_Syntax_Print.term_to_string reified)
in (FStar_Util.print2 "Reified (1) <%s> to %s\n" uu____14155 uu____14156)))));
(

let uu____14157 = (FStar_List.tl stack)
in (norm cfg env uu____14157 reified));
))))))))))
end))
end)))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head_app, args) -> begin
((

let uu____14185 = (FStar_Options.defensive ())
in (match (uu____14185) with
| true -> begin
(

let is_arg_impure = (fun uu____14197 -> (match (uu____14197) with
| (e, q) -> begin
(

let uu____14210 = (

let uu____14211 = (FStar_Syntax_Subst.compress e)
in uu____14211.FStar_Syntax_Syntax.n)
in (match (uu____14210) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t')) -> begin
(

let uu____14226 = (FStar_Syntax_Util.is_pure_effect m1)
in (not (uu____14226)))
end
| uu____14227 -> begin
false
end))
end))
in (

let uu____14228 = (

let uu____14229 = (

let uu____14240 = (FStar_Syntax_Syntax.as_arg head_app)
in (uu____14240)::args)
in (FStar_Util.for_some is_arg_impure uu____14229))
in (match (uu____14228) with
| true -> begin
(

let uu____14265 = (

let uu____14270 = (

let uu____14271 = (FStar_Syntax_Print.term_to_string head3)
in (FStar_Util.format1 "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n" uu____14271))
in ((FStar_Errors.Warning_Defensive), (uu____14270)))
in (FStar_Errors.log_issue head3.FStar_Syntax_Syntax.pos uu____14265))
end
| uu____14272 -> begin
()
end)))
end
| uu____14273 -> begin
()
end));
(

let fallback1 = (fun uu____14279 -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____14283 -> (

let uu____14284 = (FStar_Syntax_Print.term_to_string head0)
in (FStar_Util.print2 "Reified (2) <%s> to %s\n" uu____14284 ""))));
(

let uu____14285 = (FStar_List.tl stack)
in (

let uu____14286 = (FStar_Syntax_Util.mk_reify head3)
in (norm cfg env uu____14285 uu____14286)));
))
in (

let fallback2 = (fun uu____14292 -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____14296 -> (

let uu____14297 = (FStar_Syntax_Print.term_to_string head0)
in (FStar_Util.print2 "Reified (3) <%s> to %s\n" uu____14297 ""))));
(

let uu____14298 = (FStar_List.tl stack)
in (

let uu____14299 = (mk (FStar_Syntax_Syntax.Tm_meta (((head3), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) head0.FStar_Syntax_Syntax.pos)
in (norm cfg env uu____14298 uu____14299)));
))
in (

let uu____14304 = (

let uu____14305 = (FStar_Syntax_Util.un_uinst head_app)
in uu____14305.FStar_Syntax_Syntax.n)
in (match (uu____14304) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let qninfo = (FStar_TypeChecker_Env.lookup_qname cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (

let uu____14311 = (

let uu____14312 = (FStar_TypeChecker_Env.is_action cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (not (uu____14312)))
in (match (uu____14311) with
| true -> begin
(fallback1 ())
end
| uu____14313 -> begin
(

let uu____14314 = (

let uu____14315 = (FStar_TypeChecker_Env.lookup_definition_qninfo cfg.FStar_TypeChecker_Cfg.delta_level fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v qninfo)
in (FStar_Option.isNone uu____14315))
in (match (uu____14314) with
| true -> begin
(fallback2 ())
end
| uu____14326 -> begin
(

let t1 = (

let uu____14330 = (

let uu____14335 = (FStar_Syntax_Util.mk_reify head_app)
in (FStar_Syntax_Syntax.mk_Tm_app uu____14335 args))
in (uu____14330 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let uu____14338 = (FStar_List.tl stack)
in (norm cfg env uu____14338 t1)))
end))
end))))
end
| uu____14339 -> begin
(fallback1 ())
end))));
)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (uu____14341)) -> begin
(do_reify_monadic fallback cfg env stack e m t)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (

let uu____14365 = (closure_as_term cfg env t')
in (reify_lift cfg e msrc mtgt uu____14365))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____14369 -> (

let uu____14370 = (FStar_Syntax_Print.term_to_string lifted)
in (FStar_Util.print1 "Reified lift to (2): %s\n" uu____14370))));
(

let uu____14371 = (FStar_List.tl stack)
in (norm cfg env uu____14371 lifted));
))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____14492 -> (match (uu____14492) with
| (pat, wopt, tm) -> begin
(

let uu____14540 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____14540)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches1)))) head3.FStar_Syntax_Syntax.pos)
in (

let uu____14572 = (FStar_List.tl stack)
in (norm cfg env uu____14572 tm))))
end
| uu____14573 -> begin
(fallback ())
end)));
)));
))
and reify_lift : FStar_TypeChecker_Cfg.cfg  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg e msrc mtgt t -> (

let env = cfg.FStar_TypeChecker_Cfg.tcenv
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____14587 -> (

let uu____14588 = (FStar_Ident.string_of_lid msrc)
in (

let uu____14589 = (FStar_Ident.string_of_lid mtgt)
in (

let uu____14590 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14588 uu____14589 uu____14590))))));
(

let uu____14591 = ((FStar_Syntax_Util.is_pure_effect msrc) || (FStar_Syntax_Util.is_div_effect msrc))
in (match (uu____14591) with
| true -> begin
(

let ed = (

let uu____14593 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv mtgt)
in (FStar_TypeChecker_Env.get_effect_decl env uu____14593))
in (

let uu____14594 = ed.FStar_Syntax_Syntax.return_repr
in (match (uu____14594) with
| (uu____14595, return_repr) -> begin
(

let return_inst = (

let uu____14608 = (

let uu____14609 = (FStar_Syntax_Subst.compress return_repr)
in uu____14609.FStar_Syntax_Syntax.n)
in (match (uu____14608) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (uu____14615)::[]) -> begin
(

let uu____14620 = (

let uu____14627 = (

let uu____14628 = (

let uu____14635 = (

let uu____14636 = (env.FStar_TypeChecker_Env.universe_of env t)
in (uu____14636)::[])
in ((return_tm), (uu____14635)))
in FStar_Syntax_Syntax.Tm_uinst (uu____14628))
in (FStar_Syntax_Syntax.mk uu____14627))
in (uu____14620 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end
| uu____14642 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let uu____14645 = (

let uu____14652 = (

let uu____14653 = (

let uu____14670 = (

let uu____14681 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____14690 = (

let uu____14701 = (FStar_Syntax_Syntax.as_arg e)
in (uu____14701)::[])
in (uu____14681)::uu____14690))
in ((return_inst), (uu____14670)))
in FStar_Syntax_Syntax.Tm_app (uu____14653))
in (FStar_Syntax_Syntax.mk uu____14652))
in (uu____14645 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end)))
end
| uu____14749 -> begin
(

let uu____14750 = (FStar_TypeChecker_Env.monad_leq env msrc mtgt)
in (match (uu____14750) with
| FStar_Pervasives_Native.None -> begin
(

let uu____14753 = (

let uu____14754 = (FStar_Ident.text_of_lid msrc)
in (

let uu____14755 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" uu____14754 uu____14755)))
in (failwith uu____14753))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____14756; FStar_TypeChecker_Env.mtarget = uu____14757; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____14758; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(

let uu____14780 = (

let uu____14781 = (FStar_Ident.text_of_lid msrc)
in (

let uu____14782 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a non-reifiable lift (from %s to %s)" uu____14781 uu____14782)))
in (failwith uu____14780))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____14783; FStar_TypeChecker_Env.mtarget = uu____14784; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____14785; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let uu____14820 = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let uu____14821 = (FStar_Syntax_Util.mk_reify e)
in (lift uu____14820 t FStar_Syntax_Syntax.tun uu____14821)))
end))
end));
)))
and norm_pattern_args : FStar_TypeChecker_Cfg.cfg  ->  env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun uu____14891 -> (match (uu____14891) with
| (a, imp) -> begin
(

let uu____14910 = (norm cfg env [] a)
in ((uu____14910), (imp)))
end))))))
and norm_comp : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____14920 -> (

let uu____14921 = (FStar_Syntax_Print.comp_to_string comp)
in (

let uu____14922 = (FStar_Util.string_of_int (FStar_List.length env))
in (FStar_Util.print2 ">>> %s\nNormComp with with %s env elements" uu____14921 uu____14922)))));
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let t1 = (norm cfg env [] t)
in (

let uopt1 = (match (uopt) with
| FStar_Pervasives_Native.Some (u) -> begin
(

let uu____14946 = (norm_universe cfg env u)
in (FStar_All.pipe_left (fun _0_3 -> FStar_Pervasives_Native.Some (_0_3)) uu____14946))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let uu___328_14949 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t1), (uopt1))); FStar_Syntax_Syntax.pos = uu___328_14949.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___328_14949.FStar_Syntax_Syntax.vars})))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let t1 = (norm cfg env [] t)
in (

let uopt1 = (match (uopt) with
| FStar_Pervasives_Native.Some (u) -> begin
(

let uu____14971 = (norm_universe cfg env u)
in (FStar_All.pipe_left (fun _0_4 -> FStar_Pervasives_Native.Some (_0_4)) uu____14971))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let uu___329_14974 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (((t1), (uopt1))); FStar_Syntax_Syntax.pos = uu___329_14974.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___329_14974.FStar_Syntax_Syntax.vars})))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (FStar_List.mapi (fun idx uu____15019 -> (match (uu____15019) with
| (a, i) -> begin
(

let uu____15038 = (norm cfg env [] a)
in ((uu____15038), (i)))
end)))
in (

let effect_args = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in (

let flags1 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___273_15060 -> (match (uu___273_15060) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____15064 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____15064))
end
| f -> begin
f
end))))
in (

let comp_univs = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (

let result_typ = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (

let uu___330_15072 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ((

let uu___331_15075 = ct
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___331_15075.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = effect_args; FStar_Syntax_Syntax.flags = flags1})); FStar_Syntax_Syntax.pos = uu___330_15072.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___330_15072.FStar_Syntax_Syntax.vars}))))))
end);
))
and norm_binder : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env b -> (

let uu____15079 = b
in (match (uu____15079) with
| (x, imp) -> begin
(

let x1 = (

let uu___332_15087 = x
in (

let uu____15088 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___332_15087.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___332_15087.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____15088}))
in (

let imp1 = (match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____15099 = (

let uu____15100 = (closure_as_term cfg env t)
in FStar_Syntax_Syntax.Meta (uu____15100))
in FStar_Pervasives_Native.Some (uu____15099))
end
| i -> begin
i
end)
in ((x1), (imp1))))
end)))
and norm_binders : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let uu____15111 = (FStar_List.fold_left (fun uu____15145 b -> (match (uu____15145) with
| (nbs', env1) -> begin
(

let b1 = (norm_binder cfg env1 b)
in (((b1)::nbs'), ((dummy)::env1)))
end)) (([]), (env)) bs)
in (match (uu____15111) with
| (nbs, uu____15225) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags1 = (filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags)
in (

let uu____15257 = (

let uu___333_15258 = rc
in (

let uu____15259 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___333_15258.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____15259; FStar_Syntax_Syntax.residual_flags = uu___333_15258.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____15257)))
end
| uu____15268 -> begin
lopt
end))
and maybe_simplify : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack tm -> (

let tm' = (maybe_simplify_aux cfg env stack tm)
in ((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.b380) with
| true -> begin
(

let uu____15277 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____15278 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n" (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.simplify) with
| true -> begin
""
end
| uu____15279 -> begin
"NOT "
end) uu____15277 uu____15278)))
end
| uu____15280 -> begin
()
end);
tm';
)))
and norm_cb : FStar_TypeChecker_Cfg.cfg  ->  FStar_Syntax_Embeddings.norm_cb = (fun cfg uu___274_15282 -> (match (uu___274_15282) with
| FStar_Util.Inr (x) -> begin
(norm cfg [] [] x)
end
| FStar_Util.Inl (l) -> begin
(

let uu____15295 = (FStar_Syntax_DsEnv.try_lookup_lid cfg.FStar_TypeChecker_Cfg.tcenv.FStar_TypeChecker_Env.dsenv l)
in (match (uu____15295) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____15299 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____15299))
end))
end))
and maybe_simplify_aux : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack tm -> (

let tm1 = (

let uu____15307 = (norm_cb cfg)
in (reduce_primops uu____15307 cfg env tm))
in (

let uu____15314 = (FStar_All.pipe_left Prims.op_Negation cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.simplify)
in (match (uu____15314) with
| true -> begin
tm1
end
| uu____15315 -> begin
(

let w = (fun t -> (

let uu___334_15328 = t
in {FStar_Syntax_Syntax.n = uu___334_15328.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = tm1.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___334_15328.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (

let uu____15339 = (

let uu____15340 = (FStar_Syntax_Util.unmeta t)
in uu____15340.FStar_Syntax_Syntax.n)
in (match (uu____15339) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_Pervasives_Native.Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid) -> begin
FStar_Pervasives_Native.Some (false)
end
| uu____15347 -> begin
FStar_Pervasives_Native.None
end)))
in (

let rec args_are_binders = (fun args bs -> (match (((args), (bs))) with
| (((t, uu____15408))::args1, ((bv, uu____15411))::bs1) -> begin
(

let uu____15465 = (

let uu____15466 = (FStar_Syntax_Subst.compress t)
in uu____15466.FStar_Syntax_Syntax.n)
in (match (uu____15465) with
| FStar_Syntax_Syntax.Tm_name (bv') -> begin
((FStar_Syntax_Syntax.bv_eq bv bv') && (args_are_binders args1 bs1))
end
| uu____15470 -> begin
false
end))
end
| ([], []) -> begin
true
end
| (uu____15499, uu____15500) -> begin
false
end))
in (

let is_applied = (fun bs t -> ((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____15549 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____15550 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____15549 uu____15550)))
end
| uu____15551 -> begin
()
end);
(

let uu____15552 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____15552) with
| (hd1, args) -> begin
(

let uu____15591 = (

let uu____15592 = (FStar_Syntax_Subst.compress hd1)
in uu____15592.FStar_Syntax_Syntax.n)
in (match (uu____15591) with
| FStar_Syntax_Syntax.Tm_name (bv) when (args_are_binders args bs) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____15599 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____15600 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____15601 = (FStar_Syntax_Print.term_to_string hd1)
in (FStar_Util.print3 "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n" uu____15599 uu____15600 uu____15601))))
end
| uu____15602 -> begin
()
end);
FStar_Pervasives_Native.Some (bv);
)
end
| uu____15603 -> begin
FStar_Pervasives_Native.None
end))
end));
))
in (

let is_applied_maybe_squashed = (fun bs t -> ((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____15620 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____15621 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n" uu____15620 uu____15621)))
end
| uu____15622 -> begin
()
end);
(

let uu____15623 = (FStar_Syntax_Util.is_squash t)
in (match (uu____15623) with
| FStar_Pervasives_Native.Some (uu____15634, t') -> begin
(is_applied bs t')
end
| uu____15646 -> begin
(

let uu____15655 = (FStar_Syntax_Util.is_auto_squash t)
in (match (uu____15655) with
| FStar_Pervasives_Native.Some (uu____15666, t') -> begin
(is_applied bs t')
end
| uu____15678 -> begin
(is_applied bs t)
end))
end));
))
in (

let is_quantified_const = (fun bv phi -> (

let uu____15702 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____15702) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid, ((p, uu____15709))::((q, uu____15711))::[])) when (FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____15753 = (FStar_Syntax_Print.term_to_string p)
in (

let uu____15754 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print2 "WPE> p = (%s); q = (%s)\n" uu____15753 uu____15754)))
end
| uu____15755 -> begin
()
end);
(

let uu____15756 = (FStar_Syntax_Util.destruct_typ_as_formula p)
in (match (uu____15756) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15761 = (

let uu____15762 = (FStar_Syntax_Subst.compress p)
in uu____15762.FStar_Syntax_Syntax.n)
in (match (uu____15761) with
| FStar_Syntax_Syntax.Tm_bvar (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 1\n")
end
| uu____15769 -> begin
()
end);
(

let uu____15770 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (FStar_Syntax_Util.t_true))))::[]) q)
in FStar_Pervasives_Native.Some (uu____15770));
)
end
| uu____15773 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid1, ((p1, uu____15776))::[])) when (FStar_Ident.lid_equals lid1 FStar_Parser_Const.not_lid) -> begin
(

let uu____15801 = (

let uu____15802 = (FStar_Syntax_Subst.compress p1)
in uu____15802.FStar_Syntax_Syntax.n)
in (match (uu____15801) with
| FStar_Syntax_Syntax.Tm_bvar (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 2\n")
end
| uu____15809 -> begin
()
end);
(

let uu____15810 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (FStar_Syntax_Util.t_false))))::[]) q)
in FStar_Pervasives_Native.Some (uu____15810));
)
end
| uu____15813 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (bs, pats, phi1)) -> begin
(

let uu____15817 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____15817) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15822 = (is_applied_maybe_squashed bs phi1)
in (match (uu____15822) with
| FStar_Pervasives_Native.Some (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 3\n")
end
| uu____15829 -> begin
()
end);
(

let ftrue = (FStar_Syntax_Util.abs bs FStar_Syntax_Util.t_true (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let uu____15833 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (ftrue))))::[]) q)
in FStar_Pervasives_Native.Some (uu____15833)));
)
end
| uu____15836 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid1, ((p1, uu____15841))::[])) when (FStar_Ident.lid_equals lid1 FStar_Parser_Const.not_lid) -> begin
(

let uu____15866 = (is_applied_maybe_squashed bs p1)
in (match (uu____15866) with
| FStar_Pervasives_Native.Some (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 4\n")
end
| uu____15873 -> begin
()
end);
(

let ffalse = (FStar_Syntax_Util.abs bs FStar_Syntax_Util.t_false (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let uu____15877 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (ffalse))))::[]) q)
in FStar_Pervasives_Native.Some (uu____15877)));
)
end
| uu____15880 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____15883 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____15886 -> begin
FStar_Pervasives_Native.None
end));
)
end
| uu____15889 -> begin
FStar_Pervasives_Native.None
end)))
in (

let is_forall_const = (fun phi -> (

let uu____15902 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____15902) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (((bv, uu____15908))::[], uu____15909, phi')) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____15928 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____15929 = (FStar_Syntax_Print.term_to_string phi')
in (FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____15928 uu____15929)))
end
| uu____15930 -> begin
()
end);
(is_quantified_const bv phi');
)
end
| uu____15931 -> begin
FStar_Pervasives_Native.None
end)))
in (

let is_const_match = (fun phi -> (

let uu____15944 = (

let uu____15945 = (FStar_Syntax_Subst.compress phi)
in uu____15945.FStar_Syntax_Syntax.n)
in (match (uu____15944) with
| FStar_Syntax_Syntax.Tm_match (uu____15950, (br)::brs) -> begin
(

let uu____16017 = br
in (match (uu____16017) with
| (uu____16034, uu____16035, e) -> begin
(

let r = (

let uu____16056 = (simp_t e)
in (match (uu____16056) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let uu____16062 = (FStar_List.for_all (fun uu____16080 -> (match (uu____16080) with
| (uu____16093, uu____16094, e') -> begin
(

let uu____16108 = (simp_t e')
in (Prims.op_Equality uu____16108 (FStar_Pervasives_Native.Some (b))))
end)) brs)
in (match (uu____16062) with
| true -> begin
FStar_Pervasives_Native.Some (b)
end
| uu____16115 -> begin
FStar_Pervasives_Native.None
end))
end))
in r)
end))
end
| uu____16116 -> begin
FStar_Pervasives_Native.None
end)))
in (

let maybe_auto_squash = (fun t -> (

let uu____16125 = (FStar_Syntax_Util.is_sub_singleton t)
in (match (uu____16125) with
| true -> begin
t
end
| uu____16128 -> begin
(FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t)
end)))
in (

let squashed_head_un_auto_squash_args = (fun t -> (

let maybe_un_auto_squash_arg = (fun uu____16160 -> (match (uu____16160) with
| (t1, q) -> begin
(

let uu____16181 = (FStar_Syntax_Util.is_auto_squash t1)
in (match (uu____16181) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t2) -> begin
((t2), (q))
end
| uu____16213 -> begin
((t1), (q))
end))
end))
in (

let uu____16226 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____16226) with
| (head1, args) -> begin
(

let args1 = (FStar_List.map maybe_un_auto_squash_arg args)
in (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))))
in (

let rec clearly_inhabited = (fun ty -> (

let uu____16304 = (

let uu____16305 = (FStar_Syntax_Util.unmeta ty)
in uu____16305.FStar_Syntax_Syntax.n)
in (match (uu____16304) with
| FStar_Syntax_Syntax.Tm_uinst (t, uu____16309) -> begin
(clearly_inhabited t)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____16314, c) -> begin
(clearly_inhabited (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in ((((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)))
end
| uu____16338 -> begin
false
end)))
in (

let simplify1 = (fun arg -> (

let uu____16369 = (simp_t (FStar_Pervasives_Native.fst arg))
in ((uu____16369), (arg))))
in (

let uu____16382 = (is_forall_const tm1)
in (match (uu____16382) with
| FStar_Pervasives_Native.Some (tm') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____16387 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____16388 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "WPE> %s ~> %s\n" uu____16387 uu____16388)))
end
| uu____16389 -> begin
()
end);
(

let uu____16390 = (norm cfg env [] tm')
in (maybe_simplify_aux cfg env stack uu____16390));
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____16391 = (

let uu____16392 = (FStar_Syntax_Subst.compress tm1)
in uu____16392.FStar_Syntax_Syntax.n)
in (match (uu____16391) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____16396; FStar_Syntax_Syntax.vars = uu____16397}, uu____16398); FStar_Syntax_Syntax.pos = uu____16399; FStar_Syntax_Syntax.vars = uu____16400}, args) -> begin
(

let uu____16430 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____16430) with
| true -> begin
(

let uu____16431 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____16431) with
| ((FStar_Pervasives_Native.Some (true), uu____16486))::((uu____16487, (arg, uu____16489)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____16554, (arg, uu____16556)))::((FStar_Pervasives_Native.Some (true), uu____16557))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (false), uu____16622))::(uu____16623)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____16686)::((FStar_Pervasives_Native.Some (false), uu____16687))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____16750 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____16765 -> begin
(

let uu____16766 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____16766) with
| true -> begin
(

let uu____16767 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____16767) with
| ((FStar_Pervasives_Native.Some (true), uu____16822))::(uu____16823)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____16886)::((FStar_Pervasives_Native.Some (true), uu____16887))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____16950))::((uu____16951, (arg, uu____16953)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____17018, (arg, uu____17020)))::((FStar_Pervasives_Native.Some (false), uu____17021))::[] -> begin
(maybe_auto_squash arg)
end
| uu____17086 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____17101 -> begin
(

let uu____17102 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____17102) with
| true -> begin
(

let uu____17103 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____17103) with
| (uu____17158)::((FStar_Pervasives_Native.Some (true), uu____17159))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____17222))::(uu____17223)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____17286))::((uu____17287, (arg, uu____17289)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____17354, (p, uu____17356)))::((uu____17357, (q, uu____17359)))::[] -> begin
(

let uu____17424 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____17424) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____17425 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____17426 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____17441 -> begin
(

let uu____17442 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)
in (match (uu____17442) with
| true -> begin
(

let uu____17443 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____17443) with
| ((FStar_Pervasives_Native.Some (true), uu____17498))::((FStar_Pervasives_Native.Some (true), uu____17499))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____17564))::((FStar_Pervasives_Native.Some (false), uu____17565))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____17630))::((FStar_Pervasives_Native.Some (false), uu____17631))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____17696))::((FStar_Pervasives_Native.Some (true), uu____17697))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((uu____17762, (arg, uu____17764)))::((FStar_Pervasives_Native.Some (true), uu____17765))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (true), uu____17830))::((uu____17831, (arg, uu____17833)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____17898, (arg, uu____17900)))::((FStar_Pervasives_Native.Some (false), uu____17901))::[] -> begin
(

let uu____17966 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____17966))
end
| ((FStar_Pervasives_Native.Some (false), uu____17967))::((uu____17968, (arg, uu____17970)))::[] -> begin
(

let uu____18035 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____18035))
end
| ((uu____18036, (p, uu____18038)))::((uu____18039, (q, uu____18041)))::[] -> begin
(

let uu____18106 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____18106) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____18107 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____18108 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____18123 -> begin
(

let uu____18124 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____18124) with
| true -> begin
(

let uu____18125 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____18125) with
| ((FStar_Pervasives_Native.Some (true), uu____18180))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____18219))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____18258 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____18273 -> begin
(

let uu____18274 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____18274) with
| true -> begin
(match (args) with
| ((t, uu____18276))::[] -> begin
(

let uu____18301 = (

let uu____18302 = (FStar_Syntax_Subst.compress t)
in uu____18302.FStar_Syntax_Syntax.n)
in (match (uu____18301) with
| FStar_Syntax_Syntax.Tm_abs ((uu____18305)::[], body, uu____18307) -> begin
(

let uu____18342 = (simp_t body)
in (match (uu____18342) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____18345 -> begin
tm1
end))
end
| uu____18348 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____18350))))::((t, uu____18352))::[] -> begin
(

let uu____18391 = (

let uu____18392 = (FStar_Syntax_Subst.compress t)
in uu____18392.FStar_Syntax_Syntax.n)
in (match (uu____18391) with
| FStar_Syntax_Syntax.Tm_abs ((uu____18395)::[], body, uu____18397) -> begin
(

let uu____18432 = (simp_t body)
in (match (uu____18432) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| FStar_Pervasives_Native.Some (false) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____18435 -> begin
tm1
end))
end
| uu____18438 -> begin
tm1
end))
end
| uu____18439 -> begin
tm1
end)
end
| uu____18450 -> begin
(

let uu____18451 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____18451) with
| true -> begin
(match (args) with
| ((t, uu____18453))::[] -> begin
(

let uu____18478 = (

let uu____18479 = (FStar_Syntax_Subst.compress t)
in uu____18479.FStar_Syntax_Syntax.n)
in (match (uu____18478) with
| FStar_Syntax_Syntax.Tm_abs ((uu____18482)::[], body, uu____18484) -> begin
(

let uu____18519 = (simp_t body)
in (match (uu____18519) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____18522 -> begin
tm1
end))
end
| uu____18525 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____18527))))::((t, uu____18529))::[] -> begin
(

let uu____18568 = (

let uu____18569 = (FStar_Syntax_Subst.compress t)
in uu____18569.FStar_Syntax_Syntax.n)
in (match (uu____18568) with
| FStar_Syntax_Syntax.Tm_abs ((uu____18572)::[], body, uu____18574) -> begin
(

let uu____18609 = (simp_t body)
in (match (uu____18609) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| FStar_Pervasives_Native.Some (true) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____18612 -> begin
tm1
end))
end
| uu____18615 -> begin
tm1
end))
end
| uu____18616 -> begin
tm1
end)
end
| uu____18627 -> begin
(

let uu____18628 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
in (match (uu____18628) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____18629; FStar_Syntax_Syntax.vars = uu____18630}, uu____18631))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____18656; FStar_Syntax_Syntax.vars = uu____18657}, uu____18658))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____18683 -> begin
tm1
end)
end
| uu____18694 -> begin
(

let uu____18695 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.haseq_lid)
in (match (uu____18695) with
| true -> begin
(

let t_has_eq_for_sure = (fun t -> (

let haseq_lids = (FStar_Parser_Const.int_lid)::(FStar_Parser_Const.bool_lid)::(FStar_Parser_Const.unit_lid)::(FStar_Parser_Const.string_lid)::[]
in (

let uu____18705 = (

let uu____18706 = (FStar_Syntax_Subst.compress t)
in uu____18706.FStar_Syntax_Syntax.n)
in (match (uu____18705) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (FStar_All.pipe_right haseq_lids (FStar_List.existsb (fun l -> (FStar_Syntax_Syntax.fv_eq_lid fv1 l)))) -> begin
true
end
| uu____18714 -> begin
false
end))))
in (match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "1"))) with
| true -> begin
(

let t = (

let uu____18724 = (FStar_All.pipe_right args FStar_List.hd)
in (FStar_All.pipe_right uu____18724 FStar_Pervasives_Native.fst))
in (

let uu____18763 = (FStar_All.pipe_right t t_has_eq_for_sure)
in (match (uu____18763) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____18764 -> begin
(

let uu____18765 = (

let uu____18766 = (FStar_Syntax_Subst.compress t)
in uu____18766.FStar_Syntax_Syntax.n)
in (match (uu____18765) with
| FStar_Syntax_Syntax.Tm_refine (uu____18769) -> begin
(

let t1 = (FStar_Syntax_Util.unrefine t)
in (

let uu____18777 = (FStar_All.pipe_right t1 t_has_eq_for_sure)
in (match (uu____18777) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____18778 -> begin
(

let haseq_tm = (

let uu____18782 = (

let uu____18783 = (FStar_Syntax_Subst.compress tm1)
in uu____18783.FStar_Syntax_Syntax.n)
in (match (uu____18782) with
| FStar_Syntax_Syntax.Tm_app (hd1, uu____18789) -> begin
hd1
end
| uu____18814 -> begin
(failwith "Impossible! We have already checked that this is a Tm_app")
end))
in (

let uu____18817 = (

let uu____18828 = (FStar_All.pipe_right t1 FStar_Syntax_Syntax.as_arg)
in (uu____18828)::[])
in (FStar_Syntax_Util.mk_app haseq_tm uu____18817)))
end)))
end
| uu____18861 -> begin
tm1
end))
end)))
end
| uu____18862 -> begin
tm1
end))
end
| uu____18863 -> begin
(

let uu____18864 = (FStar_Syntax_Util.is_auto_squash tm1)
in (match (uu____18864) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t) when (FStar_Syntax_Util.is_sub_singleton t) -> begin
t
end
| uu____18884 -> begin
(

let uu____18893 = (

let uu____18900 = (norm_cb cfg)
in (reduce_equality uu____18900 cfg env))
in (uu____18893 tm1))
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
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____18908; FStar_Syntax_Syntax.vars = uu____18909}, args) -> begin
(

let uu____18935 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____18935) with
| true -> begin
(

let uu____18936 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____18936) with
| ((FStar_Pervasives_Native.Some (true), uu____18991))::((uu____18992, (arg, uu____18994)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____19059, (arg, uu____19061)))::((FStar_Pervasives_Native.Some (true), uu____19062))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (false), uu____19127))::(uu____19128)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____19191)::((FStar_Pervasives_Native.Some (false), uu____19192))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____19255 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19270 -> begin
(

let uu____19271 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____19271) with
| true -> begin
(

let uu____19272 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____19272) with
| ((FStar_Pervasives_Native.Some (true), uu____19327))::(uu____19328)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____19391)::((FStar_Pervasives_Native.Some (true), uu____19392))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____19455))::((uu____19456, (arg, uu____19458)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____19523, (arg, uu____19525)))::((FStar_Pervasives_Native.Some (false), uu____19526))::[] -> begin
(maybe_auto_squash arg)
end
| uu____19591 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19606 -> begin
(

let uu____19607 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____19607) with
| true -> begin
(

let uu____19608 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____19608) with
| (uu____19663)::((FStar_Pervasives_Native.Some (true), uu____19664))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____19727))::(uu____19728)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____19791))::((uu____19792, (arg, uu____19794)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____19859, (p, uu____19861)))::((uu____19862, (q, uu____19864)))::[] -> begin
(

let uu____19929 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____19929) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____19930 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19931 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19946 -> begin
(

let uu____19947 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)
in (match (uu____19947) with
| true -> begin
(

let uu____19948 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____19948) with
| ((FStar_Pervasives_Native.Some (true), uu____20003))::((FStar_Pervasives_Native.Some (true), uu____20004))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____20069))::((FStar_Pervasives_Native.Some (false), uu____20070))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____20135))::((FStar_Pervasives_Native.Some (false), uu____20136))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____20201))::((FStar_Pervasives_Native.Some (true), uu____20202))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((uu____20267, (arg, uu____20269)))::((FStar_Pervasives_Native.Some (true), uu____20270))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (true), uu____20335))::((uu____20336, (arg, uu____20338)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____20403, (arg, uu____20405)))::((FStar_Pervasives_Native.Some (false), uu____20406))::[] -> begin
(

let uu____20471 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____20471))
end
| ((FStar_Pervasives_Native.Some (false), uu____20472))::((uu____20473, (arg, uu____20475)))::[] -> begin
(

let uu____20540 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____20540))
end
| ((uu____20541, (p, uu____20543)))::((uu____20544, (q, uu____20546)))::[] -> begin
(

let uu____20611 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____20611) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20612 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20613 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20628 -> begin
(

let uu____20629 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____20629) with
| true -> begin
(

let uu____20630 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____20630) with
| ((FStar_Pervasives_Native.Some (true), uu____20685))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____20724))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20763 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20778 -> begin
(

let uu____20779 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____20779) with
| true -> begin
(match (args) with
| ((t, uu____20781))::[] -> begin
(

let uu____20806 = (

let uu____20807 = (FStar_Syntax_Subst.compress t)
in uu____20807.FStar_Syntax_Syntax.n)
in (match (uu____20806) with
| FStar_Syntax_Syntax.Tm_abs ((uu____20810)::[], body, uu____20812) -> begin
(

let uu____20847 = (simp_t body)
in (match (uu____20847) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20850 -> begin
tm1
end))
end
| uu____20853 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____20855))))::((t, uu____20857))::[] -> begin
(

let uu____20896 = (

let uu____20897 = (FStar_Syntax_Subst.compress t)
in uu____20897.FStar_Syntax_Syntax.n)
in (match (uu____20896) with
| FStar_Syntax_Syntax.Tm_abs ((uu____20900)::[], body, uu____20902) -> begin
(

let uu____20937 = (simp_t body)
in (match (uu____20937) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| FStar_Pervasives_Native.Some (false) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____20940 -> begin
tm1
end))
end
| uu____20943 -> begin
tm1
end))
end
| uu____20944 -> begin
tm1
end)
end
| uu____20955 -> begin
(

let uu____20956 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____20956) with
| true -> begin
(match (args) with
| ((t, uu____20958))::[] -> begin
(

let uu____20983 = (

let uu____20984 = (FStar_Syntax_Subst.compress t)
in uu____20984.FStar_Syntax_Syntax.n)
in (match (uu____20983) with
| FStar_Syntax_Syntax.Tm_abs ((uu____20987)::[], body, uu____20989) -> begin
(

let uu____21024 = (simp_t body)
in (match (uu____21024) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____21027 -> begin
tm1
end))
end
| uu____21030 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____21032))))::((t, uu____21034))::[] -> begin
(

let uu____21073 = (

let uu____21074 = (FStar_Syntax_Subst.compress t)
in uu____21074.FStar_Syntax_Syntax.n)
in (match (uu____21073) with
| FStar_Syntax_Syntax.Tm_abs ((uu____21077)::[], body, uu____21079) -> begin
(

let uu____21114 = (simp_t body)
in (match (uu____21114) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| FStar_Pervasives_Native.Some (true) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____21117 -> begin
tm1
end))
end
| uu____21120 -> begin
tm1
end))
end
| uu____21121 -> begin
tm1
end)
end
| uu____21132 -> begin
(

let uu____21133 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
in (match (uu____21133) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____21134; FStar_Syntax_Syntax.vars = uu____21135}, uu____21136))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____21161; FStar_Syntax_Syntax.vars = uu____21162}, uu____21163))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____21188 -> begin
tm1
end)
end
| uu____21199 -> begin
(

let uu____21200 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.haseq_lid)
in (match (uu____21200) with
| true -> begin
(

let t_has_eq_for_sure = (fun t -> (

let haseq_lids = (FStar_Parser_Const.int_lid)::(FStar_Parser_Const.bool_lid)::(FStar_Parser_Const.unit_lid)::(FStar_Parser_Const.string_lid)::[]
in (

let uu____21210 = (

let uu____21211 = (FStar_Syntax_Subst.compress t)
in uu____21211.FStar_Syntax_Syntax.n)
in (match (uu____21210) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (FStar_All.pipe_right haseq_lids (FStar_List.existsb (fun l -> (FStar_Syntax_Syntax.fv_eq_lid fv1 l)))) -> begin
true
end
| uu____21219 -> begin
false
end))))
in (match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "1"))) with
| true -> begin
(

let t = (

let uu____21229 = (FStar_All.pipe_right args FStar_List.hd)
in (FStar_All.pipe_right uu____21229 FStar_Pervasives_Native.fst))
in (

let uu____21264 = (FStar_All.pipe_right t t_has_eq_for_sure)
in (match (uu____21264) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____21265 -> begin
(

let uu____21266 = (

let uu____21267 = (FStar_Syntax_Subst.compress t)
in uu____21267.FStar_Syntax_Syntax.n)
in (match (uu____21266) with
| FStar_Syntax_Syntax.Tm_refine (uu____21270) -> begin
(

let t1 = (FStar_Syntax_Util.unrefine t)
in (

let uu____21278 = (FStar_All.pipe_right t1 t_has_eq_for_sure)
in (match (uu____21278) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____21279 -> begin
(

let haseq_tm = (

let uu____21283 = (

let uu____21284 = (FStar_Syntax_Subst.compress tm1)
in uu____21284.FStar_Syntax_Syntax.n)
in (match (uu____21283) with
| FStar_Syntax_Syntax.Tm_app (hd1, uu____21290) -> begin
hd1
end
| uu____21315 -> begin
(failwith "Impossible! We have already checked that this is a Tm_app")
end))
in (

let uu____21318 = (

let uu____21329 = (FStar_All.pipe_right t1 FStar_Syntax_Syntax.as_arg)
in (uu____21329)::[])
in (FStar_Syntax_Util.mk_app haseq_tm uu____21318)))
end)))
end
| uu____21362 -> begin
tm1
end))
end)))
end
| uu____21363 -> begin
tm1
end))
end
| uu____21364 -> begin
(

let uu____21365 = (FStar_Syntax_Util.is_auto_squash tm1)
in (match (uu____21365) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t) when (FStar_Syntax_Util.is_sub_singleton t) -> begin
t
end
| uu____21385 -> begin
(

let uu____21394 = (

let uu____21401 = (norm_cb cfg)
in (reduce_equality uu____21401 cfg env))
in (uu____21394 tm1))
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

let uu____21414 = (simp_t t)
in (match (uu____21414) with
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
| FStar_Syntax_Syntax.Tm_match (uu____21417) -> begin
(

let uu____21440 = (is_const_match tm1)
in (match (uu____21440) with
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
| uu____21443 -> begin
tm1
end))
end))))))))))))))
end))))
and rebuild : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____21453 -> ((

let uu____21455 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____21456 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____21457 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____21464 = (

let uu____21465 = (

let uu____21468 = (firstn (Prims.parse_int "4") stack)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____21468))
in (stack_to_string uu____21465))
in (FStar_Util.print4 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n" uu____21455 uu____21456 uu____21457 uu____21464)))));
(

let uu____21491 = (FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv (FStar_Options.Other ("NormRebuild")))
in (match (uu____21491) with
| true -> begin
(

let uu____21492 = (FStar_Syntax_Util.unbound_variables t)
in (match (uu____21492) with
| [] -> begin
()
end
| bvs -> begin
((

let uu____21499 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____21500 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____21501 = (

let uu____21502 = (FStar_All.pipe_right bvs (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right uu____21502 (FStar_String.concat ", ")))
in (FStar_Util.print3 "!!! Rebuild (%s) %s, free vars=%s\n" uu____21499 uu____21500 uu____21501))));
(failwith "DIE!");
)
end))
end
| uu____21511 -> begin
()
end));
)));
(

let f_opt = (is_fext_on_domain t)
in (

let uu____21515 = ((FStar_All.pipe_right f_opt FStar_Util.is_some) && (match (stack) with
| (Arg (uu____21520))::uu____21521 -> begin
true
end
| uu____21530 -> begin
false
end))
in (match (uu____21515) with
| true -> begin
(

let uu____21531 = (FStar_All.pipe_right f_opt FStar_Util.must)
in (FStar_All.pipe_right uu____21531 (norm cfg env stack)))
end
| uu____21534 -> begin
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

let uu____21543 = (

let uu____21544 = (

let uu____21545 = (FStar_Util.time_diff time_then time_now)
in (FStar_Pervasives_Native.snd uu____21545))
in (FStar_Util.string_of_int uu____21544))
in (

let uu____21550 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____21551 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized term (%s ms) %s\n\tto term %s\n" uu____21543 uu____21550 uu____21551)))))
end
| uu____21552 -> begin
()
end);
(rebuild cfg env stack1 t1);
)
end
| (Cfg (cfg1))::stack1 -> begin
(rebuild cfg1 env stack1 t1)
end
| (Meta (uu____21557, m, r))::stack1 -> begin
(

let t2 = (mk (FStar_Syntax_Syntax.Tm_meta (((t1), (m)))) r)
in (rebuild cfg env stack1 t2))
end
| (MemoLazy (r))::stack1 -> begin
((set_memo cfg r ((env), (t1)));
(FStar_TypeChecker_Cfg.log cfg (fun uu____21608 -> (

let uu____21609 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____21609))));
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

let uu____21647 = (

let uu___335_21648 = (FStar_Syntax_Util.abs bs1 t1 lopt1)
in {FStar_Syntax_Syntax.n = uu___335_21648.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___335_21648.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack1 uu____21647))))
end
| (Arg (Univ (uu____21651), uu____21652, uu____21653))::uu____21654 -> begin
(failwith "Impossible")
end
| (Arg (Dummy, uu____21657, uu____21658))::uu____21659 -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack1 -> begin
(

let t2 = (FStar_Syntax_Syntax.mk_Tm_uinst t1 us)
in (rebuild cfg env stack1 t2))
end
| (Arg (Clos (env_arg, tm, uu____21674, uu____21675), aq, r))::stack1 when (

let uu____21725 = (head_of t1)
in (FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____21725)) -> begin
(

let t2 = (

let uu____21729 = (

let uu____21734 = (

let uu____21735 = (closure_as_term cfg env_arg tm)
in ((uu____21735), (aq)))
in (FStar_Syntax_Syntax.extend_app t1 uu____21734))
in (uu____21729 FStar_Pervasives_Native.None r))
in (rebuild cfg env stack1 t2))
end
| (Arg (Clos (env_arg, tm, m, uu____21747), aq, r))::stack1 -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____21800 -> (

let uu____21801 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" uu____21801))));
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
| uu____21810 -> begin
(

let stack2 = (App (((env), (t1), (aq), (r))))::stack1
in (norm cfg env_arg stack2 tm))
end)
end
| uu____21814 -> begin
(

let uu____21815 = (FStar_ST.op_Bang m)
in (match (uu____21815) with
| FStar_Pervasives_Native.None -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.hnf) with
| true -> begin
(

let arg = (closure_as_term cfg env_arg tm)
in (

let t2 = (FStar_Syntax_Syntax.extend_app t1 ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack1 t2)))
end
| uu____21919 -> begin
(

let stack2 = (MemoLazy (m))::(App (((env), (t1), (aq), (r))))::stack1
in (norm cfg env_arg stack2 tm))
end)
end
| FStar_Pervasives_Native.Some (uu____21956, a) -> begin
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

let fallback = (fun msg uu____22011 -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____22015 -> (

let uu____22016 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not reifying%s: %s\n" msg uu____22016))));
(

let t2 = (FStar_Syntax_Syntax.extend_app head1 ((t1), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack' t2));
))
in (

let uu____22024 = (

let uu____22025 = (FStar_Syntax_Subst.compress t1)
in uu____22025.FStar_Syntax_Syntax.n)
in (match (uu____22024) with
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic (m, ty)) -> begin
(do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty)
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, ty)) -> begin
(

let lifted = (

let uu____22052 = (closure_as_term cfg env1 ty)
in (reify_lift cfg t2 msrc mtgt uu____22052))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____22056 -> (

let uu____22057 = (FStar_Syntax_Print.term_to_string lifted)
in (FStar_Util.print1 "Reified lift to (1): %s\n" uu____22057))));
(

let uu____22058 = (FStar_List.tl stack)
in (norm cfg env1 uu____22058 lifted));
))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____22059)); FStar_Syntax_Syntax.pos = uu____22060; FStar_Syntax_Syntax.vars = uu____22061}, ((e, uu____22063))::[]) -> begin
(norm cfg env1 stack' e)
end
| FStar_Syntax_Syntax.Tm_app (uu____22102) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.primops -> begin
(

let uu____22119 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____22119) with
| (hd1, args) -> begin
(

let uu____22162 = (

let uu____22163 = (FStar_Syntax_Util.un_uinst hd1)
in uu____22163.FStar_Syntax_Syntax.n)
in (match (uu____22162) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____22167 = (FStar_TypeChecker_Cfg.find_prim_step cfg fv)
in (match (uu____22167) with
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Cfg.name = uu____22170; FStar_TypeChecker_Cfg.arity = uu____22171; FStar_TypeChecker_Cfg.univ_arity = uu____22172; FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.Some (n1); FStar_TypeChecker_Cfg.strong_reduction_ok = uu____22174; FStar_TypeChecker_Cfg.requires_binder_substitution = uu____22175; FStar_TypeChecker_Cfg.interpretation = uu____22176; FStar_TypeChecker_Cfg.interpretation_nbe = uu____22177}) when (Prims.op_Equality (FStar_List.length args) n1) -> begin
(norm cfg env1 stack' t1)
end
| uu____22207 -> begin
(fallback " (3)" ())
end))
end
| uu____22210 -> begin
(fallback " (4)" ())
end))
end))
end
| uu____22211 -> begin
(fallback " (2)" ())
end))))
end
| (App (env1, head1, aq, r))::stack1 -> begin
(

let t2 = (FStar_Syntax_Syntax.extend_app head1 ((t1), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack1 t2))
end
| (Match (env', branches, cfg1, r))::stack1 -> begin
((FStar_TypeChecker_Cfg.log cfg1 (fun uu____22236 -> (

let uu____22237 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" uu____22237))));
(

let scrutinee_env = env
in (

let env1 = env'
in (

let scrutinee = t1
in (

let norm_and_rebuild_match = (fun uu____22246 -> ((FStar_TypeChecker_Cfg.log cfg1 (fun uu____22251 -> (

let uu____22252 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____22253 = (

let uu____22254 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____22281 -> (match (uu____22281) with
| (p, uu____22291, uu____22292) -> begin
(FStar_Syntax_Print.pat_to_string p)
end))))
in (FStar_All.pipe_right uu____22254 (FStar_String.concat "\n\t")))
in (FStar_Util.print2 "match is irreducible: scrutinee=%s\nbranches=%s\n" uu____22252 uu____22253)))));
(

let whnf = (cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak || cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.hnf)
in (

let cfg_exclude_zeta = (

let new_delta = (FStar_All.pipe_right cfg1.FStar_TypeChecker_Cfg.delta_level (FStar_List.filter (fun uu___275_22309 -> (match (uu___275_22309) with
| FStar_TypeChecker_Env.InliningDelta -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| uu____22310 -> begin
false
end))))
in (

let steps = (

let uu___336_22312 = cfg1.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___336_22312.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___336_22312.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = false; FStar_TypeChecker_Cfg.weak = uu___336_22312.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___336_22312.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___336_22312.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___336_22312.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_only = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_fully = uu___336_22312.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_tac = false; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___336_22312.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___336_22312.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___336_22312.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___336_22312.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___336_22312.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___336_22312.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___336_22312.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___336_22312.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___336_22312.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___336_22312.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___336_22312.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___336_22312.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___336_22312.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___336_22312.FStar_TypeChecker_Cfg.for_extraction})
in (

let uu___337_22317 = cfg1
in {FStar_TypeChecker_Cfg.steps = steps; FStar_TypeChecker_Cfg.tcenv = uu___337_22317.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___337_22317.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = new_delta; FStar_TypeChecker_Cfg.primitive_steps = uu___337_22317.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___337_22317.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___337_22317.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___337_22317.FStar_TypeChecker_Cfg.reifying})))
in (

let norm_or_whnf = (fun env2 t2 -> (match (whnf) with
| true -> begin
(closure_as_term cfg_exclude_zeta env2 t2)
end
| uu____22329 -> begin
(norm cfg_exclude_zeta env2 [] t2)
end))
in (

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____22389) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____22418 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____22502 uu____22503 -> (match (((uu____22502), (uu____22503))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____22642 = (norm_pat env3 p1)
in (match (uu____22642) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____22418) with
| (pats1, env3) -> begin
(((

let uu___338_22804 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___338_22804.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___339_22823 = x
in (

let uu____22824 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___339_22823.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___339_22823.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____22824}))
in (((

let uu___340_22838 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___340_22838.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___341_22849 = x
in (

let uu____22850 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___341_22849.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___341_22849.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____22850}))
in (((

let uu___342_22864 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___342_22864.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t2) -> begin
(

let x1 = (

let uu___343_22880 = x
in (

let uu____22881 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___343_22880.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___343_22880.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____22881}))
in (

let t3 = (norm_or_whnf env2 t2)
in (((

let uu___344_22896 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t3))); FStar_Syntax_Syntax.p = uu___344_22896.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let branches1 = (match (env1) with
| [] when whnf -> begin
branches
end
| uu____22940 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch1 -> (

let uu____22970 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____22970) with
| (p, wopt, e) -> begin
(

let uu____22990 = (norm_pat env1 p)
in (match (uu____22990) with
| (p1, env2) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____23045 = (norm_or_whnf env2 w)
in FStar_Pervasives_Native.Some (uu____23045))
end)
in (

let e1 = (norm_or_whnf env2 e)
in (FStar_Syntax_Util.branch ((p1), (wopt1), (e1)))))
end))
end)))))
end)
in (

let scrutinee1 = (

let uu____23062 = ((((cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.iota && (not (cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak))) && (not (cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars))) && cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee) && (maybe_weakly_reduced scrutinee))
in (match (uu____23062) with
| true -> begin
(norm (

let uu___345_23067 = cfg1
in {FStar_TypeChecker_Cfg.steps = (

let uu___346_23070 = cfg1.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___346_23070.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___346_23070.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___346_23070.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___346_23070.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___346_23070.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___346_23070.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___346_23070.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___346_23070.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___346_23070.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___346_23070.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___346_23070.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___346_23070.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___346_23070.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___346_23070.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___346_23070.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___346_23070.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___346_23070.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___346_23070.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___346_23070.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___346_23070.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___346_23070.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___346_23070.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___346_23070.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = false; FStar_TypeChecker_Cfg.nbe_step = uu___346_23070.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___346_23070.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___345_23067.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___345_23067.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___345_23067.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___345_23067.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___345_23067.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___345_23067.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___345_23067.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___345_23067.FStar_TypeChecker_Cfg.reifying}) scrutinee_env [] scrutinee)
end
| uu____23071 -> begin
scrutinee
end))
in (

let uu____23072 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee1), (branches1)))) r)
in (rebuild cfg1 env1 stack1 uu____23072))))))));
))
in (

let rec is_cons = (fun head1 -> (

let uu____23097 = (

let uu____23098 = (FStar_Syntax_Subst.compress head1)
in uu____23098.FStar_Syntax_Syntax.n)
in (match (uu____23097) with
| FStar_Syntax_Syntax.Tm_uinst (h, uu____23102) -> begin
(is_cons h)
end
| FStar_Syntax_Syntax.Tm_constant (uu____23107) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____23108; FStar_Syntax_Syntax.fv_delta = uu____23109; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____23110; FStar_Syntax_Syntax.fv_delta = uu____23111; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____23112))}) -> begin
true
end
| uu____23119 -> begin
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

let uu____23283 = (FStar_Syntax_Util.head_and_args scrutinee2)
in (match (uu____23283) with
| (head1, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____23376) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (FStar_Const.eq_const s s') -> begin
FStar_Util.Inl ([])
end
| uu____23415 -> begin
(

let uu____23416 = (

let uu____23417 = (is_cons head1)
in (not (uu____23417)))
in FStar_Util.Inr (uu____23416))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let uu____23442 = (

let uu____23443 = (FStar_Syntax_Util.un_uinst head1)
in uu____23443.FStar_Syntax_Syntax.n)
in (match (uu____23442) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| uu____23461 -> begin
(

let uu____23462 = (

let uu____23463 = (is_cons head1)
in (not (uu____23463)))
in FStar_Util.Inr (uu____23462))
end))
end)
end)))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t2, uu____23546))::rest_a, ((p1, uu____23549))::rest_p) -> begin
(

let uu____23603 = (matches_pat t2 p1)
in (match (uu____23603) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____23652 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee1 p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p1, wopt, b))::rest -> begin
(

let uu____23772 = (matches_pat scrutinee1 p1)
in (match (uu____23772) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee1 rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
((FStar_TypeChecker_Cfg.log cfg1 (fun uu____23812 -> (

let uu____23813 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____23814 = (

let uu____23815 = (FStar_List.map (fun uu____23825 -> (match (uu____23825) with
| (uu____23830, t2) -> begin
(FStar_Syntax_Print.term_to_string t2)
end)) s)
in (FStar_All.pipe_right uu____23815 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" uu____23813 uu____23814)))));
(

let env0 = env1
in (

let env2 = (FStar_List.fold_left (fun env2 uu____23862 -> (match (uu____23862) with
| (bv, t2) -> begin
(

let uu____23885 = (

let uu____23892 = (

let uu____23895 = (FStar_Syntax_Syntax.mk_binder bv)
in FStar_Pervasives_Native.Some (uu____23895))
in (

let uu____23896 = (

let uu____23897 = (

let uu____23928 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ((([]), (t2)))))
in (([]), (t2), (uu____23928), (false)))
in Clos (uu____23897))
in ((uu____23892), (uu____23896))))
in (uu____23885)::env2)
end)) env1 s)
in (

let uu____24041 = (guard_when_clause wopt b rest)
in (norm cfg1 env2 stack1 uu____24041))));
)
end))
end))
in (match (cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.iota) with
| true -> begin
(matches scrutinee branches)
end
| uu____24042 -> begin
(norm_and_rebuild_match ())
end)))))))));
)
end))
end)));
))


let normalize_with_primitive_steps : FStar_TypeChecker_Cfg.primitive_step Prims.list  ->  FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun ps s e t -> (

let c = (FStar_TypeChecker_Cfg.config' ps s e)
in ((FStar_TypeChecker_Cfg.log_cfg c (fun uu____24071 -> (

let uu____24072 = (FStar_TypeChecker_Cfg.cfg_to_string c)
in (FStar_Util.print1 "Cfg = %s\n" uu____24072))));
(

let uu____24073 = (is_nbe_request s)
in (match (uu____24073) with
| true -> begin
((FStar_TypeChecker_Cfg.log_top c (fun uu____24077 -> (

let uu____24078 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Starting NBE for (%s) {\n" uu____24078))));
(FStar_TypeChecker_Cfg.log_top c (fun uu____24082 -> (

let uu____24083 = (FStar_TypeChecker_Cfg.cfg_to_string c)
in (FStar_Util.print1 ">>> cfg = %s\n" uu____24083))));
(

let r = (nbe_eval c s t)
in ((FStar_TypeChecker_Cfg.log_top c (fun uu____24088 -> (

let uu____24089 = (FStar_Syntax_Print.term_to_string r)
in (FStar_Util.print1 "}\nNormalization result = (%s)\n" uu____24089))));
r;
));
)
end
| uu____24090 -> begin
((FStar_TypeChecker_Cfg.log_top c (fun uu____24094 -> (

let uu____24095 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Starting normalizer for (%s) {\n" uu____24095))));
(FStar_TypeChecker_Cfg.log_top c (fun uu____24099 -> (

let uu____24100 = (FStar_TypeChecker_Cfg.cfg_to_string c)
in (FStar_Util.print1 ">>> cfg = %s\n" uu____24100))));
(

let r = (norm c [] [] t)
in ((FStar_TypeChecker_Cfg.log_top c (fun uu____24111 -> (

let uu____24112 = (FStar_Syntax_Print.term_to_string r)
in (FStar_Util.print1 "}\nNormalization result = (%s)\n" uu____24112))));
r;
));
)
end));
)))


let normalize : FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (normalize_with_primitive_steps [] s e t))


let normalize_comp : FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (

let uu____24143 = (FStar_TypeChecker_Cfg.config s e)
in (norm_comp uu____24143 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let uu____24160 = (FStar_TypeChecker_Cfg.config [] env)
in (norm_universe uu____24160 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (

let cfg = (FStar_TypeChecker_Cfg.config ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.EraseUniverses)::[]) env)
in (

let non_info = (fun t -> (

let uu____24184 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____24184)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____24191) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let uu___347_24210 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.pos = uu___347_24210.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___347_24210.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____24217 = ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ))
in (match (uu____24217) with
| true -> begin
(

let ct1 = (

let uu____24219 = (downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)
in (match (uu____24219) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let flags1 = (

let uu____24226 = (FStar_Ident.lid_equals pure_eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____24226) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::ct.FStar_Syntax_Syntax.flags
end
| uu____24229 -> begin
ct.FStar_Syntax_Syntax.flags
end))
in (

let uu___348_24230 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___348_24230.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = uu___348_24230.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___348_24230.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags1}))
end
| FStar_Pervasives_Native.None -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev cfg.FStar_TypeChecker_Cfg.tcenv c)
in (

let uu___349_24232 = ct1
in {FStar_Syntax_Syntax.comp_univs = uu___349_24232.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu___349_24232.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___349_24232.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___349_24232.FStar_Syntax_Syntax.flags}))
end))
in (

let uu___350_24233 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___350_24233.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___350_24233.FStar_Syntax_Syntax.vars}))
end
| uu____24234 -> begin
c
end)))
end
| uu____24235 -> begin
c
end))))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (FStar_TypeChecker_Cfg.config ((FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (

let uu____24253 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____24253)))
in (

let uu____24260 = ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ))
in (match (uu____24260) with
| true -> begin
(

let uu____24261 = (downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____24261) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(FStar_Syntax_Syntax.mk_lcomp pure_eff lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____24267 -> (

let uu____24268 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (ghost_to_pure env uu____24268))))
end
| FStar_Pervasives_Native.None -> begin
lc
end))
end
| uu____24269 -> begin
lc
end)))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (

let t1 = (FStar_All.try_with (fun uu___352_24282 -> (match (()) with
| () -> begin
(normalize ((FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env t)
end)) (fun uu___351_24285 -> ((

let uu____24287 = (

let uu____24292 = (

let uu____24293 = (FStar_Util.message_of_exn uu___351_24285)
in (FStar_Util.format1 "Normalization failed with error %s\n" uu____24293))
in ((FStar_Errors.Warning_NormalizationFailure), (uu____24292)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____24287));
t;
)))
in (FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let c1 = (FStar_All.try_with (fun uu___354_24307 -> (match (()) with
| () -> begin
(

let uu____24308 = (FStar_TypeChecker_Cfg.config ((FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env)
in (norm_comp uu____24308 [] c))
end)) (fun uu___353_24317 -> ((

let uu____24319 = (

let uu____24324 = (

let uu____24325 = (FStar_Util.message_of_exn uu___353_24317)
in (FStar_Util.format1 "Normalization failed with error %s\n" uu____24325))
in ((FStar_Errors.Warning_NormalizationFailure), (uu____24324)))
in (FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____24319));
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

let uu____24370 = (

let uu____24371 = (

let uu____24378 = (FStar_Syntax_Util.mk_conj_simp phi1 phi)
in ((y), (uu____24378)))
in FStar_Syntax_Syntax.Tm_refine (uu____24371))
in (mk uu____24370 t01.FStar_Syntax_Syntax.pos))
end
| uu____24383 -> begin
t2
end))
end
| uu____24384 -> begin
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
| uu____24429 -> begin
[]
end) ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.CompressUvars)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota))::(FStar_TypeChecker_Env.NoFullNorm)::[])) env t))


let reduce_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions false env t))


let remove_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions true env t))


let eta_expand_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e t_e -> (

let uu____24465 = (FStar_Syntax_Util.arrow_formals_comp t_e)
in (match (uu____24465) with
| (formals, c) -> begin
(match (formals) with
| [] -> begin
e
end
| uu____24502 -> begin
(

let uu____24511 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____24511) with
| (actuals, uu____24521, uu____24522) -> begin
(match ((Prims.op_Equality (FStar_List.length actuals) (FStar_List.length formals))) with
| true -> begin
e
end
| uu____24539 -> begin
(

let uu____24540 = (FStar_All.pipe_right formals FStar_Syntax_Util.args_of_binders)
in (match (uu____24540) with
| (binders, args) -> begin
(

let uu____24551 = (FStar_Syntax_Syntax.mk_Tm_app e args FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Util.abs binders uu____24551 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c)))))
end))
end)
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(eta_expand_with_type env t x.FStar_Syntax_Syntax.sort)
end
| uu____24565 -> begin
(

let uu____24566 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____24566) with
| (head1, args) -> begin
(

let uu____24609 = (

let uu____24610 = (FStar_Syntax_Subst.compress head1)
in uu____24610.FStar_Syntax_Syntax.n)
in (match (uu____24609) with
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____24631 = (

let uu____24646 = (FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Syntax_Util.arrow_formals uu____24646))
in (match (uu____24631) with
| (formals, _tres) -> begin
(match ((Prims.op_Equality (FStar_List.length formals) (FStar_List.length args))) with
| true -> begin
t
end
| uu____24683 -> begin
(

let uu____24684 = (env.FStar_TypeChecker_Env.type_of (

let uu___355_24692 = env
in {FStar_TypeChecker_Env.solver = uu___355_24692.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___355_24692.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___355_24692.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___355_24692.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___355_24692.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___355_24692.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___355_24692.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___355_24692.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___355_24692.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___355_24692.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___355_24692.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___355_24692.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___355_24692.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___355_24692.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___355_24692.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___355_24692.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___355_24692.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___355_24692.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___355_24692.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___355_24692.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___355_24692.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___355_24692.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___355_24692.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___355_24692.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___355_24692.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___355_24692.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___355_24692.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___355_24692.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___355_24692.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___355_24692.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___355_24692.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___355_24692.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___355_24692.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___355_24692.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___355_24692.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___355_24692.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___355_24692.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___355_24692.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___355_24692.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___355_24692.FStar_TypeChecker_Env.nbe}) t)
in (match (uu____24684) with
| (uu____24693, ty, uu____24695) -> begin
(eta_expand_with_type env t ty)
end))
end)
end))
end
| uu____24696 -> begin
(

let uu____24697 = (env.FStar_TypeChecker_Env.type_of (

let uu___356_24705 = env
in {FStar_TypeChecker_Env.solver = uu___356_24705.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___356_24705.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___356_24705.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___356_24705.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___356_24705.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___356_24705.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___356_24705.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___356_24705.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___356_24705.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___356_24705.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___356_24705.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___356_24705.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___356_24705.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___356_24705.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___356_24705.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___356_24705.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___356_24705.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___356_24705.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___356_24705.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___356_24705.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___356_24705.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___356_24705.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___356_24705.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___356_24705.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___356_24705.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___356_24705.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___356_24705.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___356_24705.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___356_24705.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___356_24705.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___356_24705.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___356_24705.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___356_24705.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___356_24705.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___356_24705.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___356_24705.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___356_24705.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___356_24705.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___356_24705.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___356_24705.FStar_TypeChecker_Env.nbe}) t)
in (match (uu____24697) with
| (uu____24706, ty, uu____24708) -> begin
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

let uu___357_24789 = x
in (

let uu____24790 = (elim_delayed_subst_term x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___357_24789.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___357_24789.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____24790})))
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____24793) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_bvar (uu____24816) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_name (uu____24817) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_fvar (uu____24818) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uinst (uu____24819) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_constant (uu____24826) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (uu____24827) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_lazy (uu____24828) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t1
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, rc_opt) -> begin
(

let elim_rc = (fun rc -> (

let uu___358_24862 = rc
in (

let uu____24863 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ elim_delayed_subst_term)
in (

let uu____24872 = (elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags)
in {FStar_Syntax_Syntax.residual_effect = uu___358_24862.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____24863; FStar_Syntax_Syntax.residual_flags = uu____24872}))))
in (

let uu____24875 = (

let uu____24876 = (

let uu____24895 = (elim_delayed_subst_binders bs)
in (

let uu____24904 = (elim_delayed_subst_term t2)
in (

let uu____24907 = (FStar_Util.map_opt rc_opt elim_rc)
in ((uu____24895), (uu____24904), (uu____24907)))))
in FStar_Syntax_Syntax.Tm_abs (uu____24876))
in (mk1 uu____24875)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____24944 = (

let uu____24945 = (

let uu____24960 = (elim_delayed_subst_binders bs)
in (

let uu____24969 = (elim_delayed_subst_comp c)
in ((uu____24960), (uu____24969))))
in FStar_Syntax_Syntax.Tm_arrow (uu____24945))
in (mk1 uu____24944))
end
| FStar_Syntax_Syntax.Tm_refine (bv, phi) -> begin
(

let uu____24988 = (

let uu____24989 = (

let uu____24996 = (elim_bv bv)
in (

let uu____24997 = (elim_delayed_subst_term phi)
in ((uu____24996), (uu____24997))))
in FStar_Syntax_Syntax.Tm_refine (uu____24989))
in (mk1 uu____24988))
end
| FStar_Syntax_Syntax.Tm_app (t2, args) -> begin
(

let uu____25028 = (

let uu____25029 = (

let uu____25046 = (elim_delayed_subst_term t2)
in (

let uu____25049 = (elim_delayed_subst_args args)
in ((uu____25046), (uu____25049))))
in FStar_Syntax_Syntax.Tm_app (uu____25029))
in (mk1 uu____25028))
end
| FStar_Syntax_Syntax.Tm_match (t2, branches) -> begin
(

let rec elim_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu___359_25121 = p
in (

let uu____25122 = (

let uu____25123 = (elim_bv x)
in FStar_Syntax_Syntax.Pat_var (uu____25123))
in {FStar_Syntax_Syntax.v = uu____25122; FStar_Syntax_Syntax.p = uu___359_25121.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu___360_25125 = p
in (

let uu____25126 = (

let uu____25127 = (elim_bv x)
in FStar_Syntax_Syntax.Pat_wild (uu____25127))
in {FStar_Syntax_Syntax.v = uu____25126; FStar_Syntax_Syntax.p = uu___360_25125.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let uu___361_25134 = p
in (

let uu____25135 = (

let uu____25136 = (

let uu____25143 = (elim_bv x)
in (

let uu____25144 = (elim_delayed_subst_term t0)
in ((uu____25143), (uu____25144))))
in FStar_Syntax_Syntax.Pat_dot_term (uu____25136))
in {FStar_Syntax_Syntax.v = uu____25135; FStar_Syntax_Syntax.p = uu___361_25134.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu___362_25167 = p
in (

let uu____25168 = (

let uu____25169 = (

let uu____25182 = (FStar_List.map (fun uu____25205 -> (match (uu____25205) with
| (x, b) -> begin
(

let uu____25218 = (elim_pat x)
in ((uu____25218), (b)))
end)) pats)
in ((fv), (uu____25182)))
in FStar_Syntax_Syntax.Pat_cons (uu____25169))
in {FStar_Syntax_Syntax.v = uu____25168; FStar_Syntax_Syntax.p = uu___362_25167.FStar_Syntax_Syntax.p}))
end
| uu____25231 -> begin
p
end))
in (

let elim_branch = (fun uu____25255 -> (match (uu____25255) with
| (pat, wopt, t3) -> begin
(

let uu____25281 = (elim_pat pat)
in (

let uu____25284 = (FStar_Util.map_opt wopt elim_delayed_subst_term)
in (

let uu____25287 = (elim_delayed_subst_term t3)
in ((uu____25281), (uu____25284), (uu____25287)))))
end))
in (

let uu____25292 = (

let uu____25293 = (

let uu____25316 = (elim_delayed_subst_term t2)
in (

let uu____25319 = (FStar_List.map elim_branch branches)
in ((uu____25316), (uu____25319))))
in FStar_Syntax_Syntax.Tm_match (uu____25293))
in (mk1 uu____25292))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, a, lopt) -> begin
(

let elim_ascription = (fun uu____25450 -> (match (uu____25450) with
| (tc, topt) -> begin
(

let uu____25485 = (match (tc) with
| FStar_Util.Inl (t3) -> begin
(

let uu____25495 = (elim_delayed_subst_term t3)
in FStar_Util.Inl (uu____25495))
end
| FStar_Util.Inr (c) -> begin
(

let uu____25497 = (elim_delayed_subst_comp c)
in FStar_Util.Inr (uu____25497))
end)
in (

let uu____25498 = (FStar_Util.map_opt topt elim_delayed_subst_term)
in ((uu____25485), (uu____25498))))
end))
in (

let uu____25507 = (

let uu____25508 = (

let uu____25535 = (elim_delayed_subst_term t2)
in (

let uu____25538 = (elim_ascription a)
in ((uu____25535), (uu____25538), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____25508))
in (mk1 uu____25507)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t2) -> begin
(

let elim_lb = (fun lb -> (

let uu___363_25599 = lb
in (

let uu____25600 = (elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____25603 = (elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___363_25599.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___363_25599.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____25600; FStar_Syntax_Syntax.lbeff = uu___363_25599.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____25603; FStar_Syntax_Syntax.lbattrs = uu___363_25599.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___363_25599.FStar_Syntax_Syntax.lbpos}))))
in (

let uu____25606 = (

let uu____25607 = (

let uu____25620 = (

let uu____25627 = (FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs))
in (((FStar_Pervasives_Native.fst lbs)), (uu____25627)))
in (

let uu____25636 = (elim_delayed_subst_term t2)
in ((uu____25620), (uu____25636))))
in FStar_Syntax_Syntax.Tm_let (uu____25607))
in (mk1 uu____25606)))
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uvar (((u), (s)))))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi)
in (

let uu____25680 = (

let uu____25681 = (

let uu____25688 = (elim_delayed_subst_term tm)
in ((uu____25688), (qi1)))
in FStar_Syntax_Syntax.Tm_quoted (uu____25681))
in (mk1 uu____25680)))
end
| FStar_Syntax_Syntax.Tm_meta (t2, md) -> begin
(

let uu____25699 = (

let uu____25700 = (

let uu____25707 = (elim_delayed_subst_term t2)
in (

let uu____25710 = (elim_delayed_subst_meta md)
in ((uu____25707), (uu____25710))))
in FStar_Syntax_Syntax.Tm_meta (uu____25700))
in (mk1 uu____25699))
end)))))
and elim_delayed_subst_cflags : FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun flags1 -> (FStar_List.map (fun uu___276_25719 -> (match (uu___276_25719) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____25723 = (elim_delayed_subst_term t)
in FStar_Syntax_Syntax.DECREASES (uu____25723))
end
| f -> begin
f
end)) flags1))
and elim_delayed_subst_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun c -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____25746 = (

let uu____25747 = (

let uu____25756 = (elim_delayed_subst_term t)
in ((uu____25756), (uopt)))
in FStar_Syntax_Syntax.Total (uu____25747))
in (mk1 uu____25746))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____25773 = (

let uu____25774 = (

let uu____25783 = (elim_delayed_subst_term t)
in ((uu____25783), (uopt)))
in FStar_Syntax_Syntax.GTotal (uu____25774))
in (mk1 uu____25773))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___364_25792 = ct
in (

let uu____25793 = (elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____25796 = (elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args)
in (

let uu____25807 = (elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu___364_25792.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___364_25792.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____25793; FStar_Syntax_Syntax.effect_args = uu____25796; FStar_Syntax_Syntax.flags = uu____25807}))))
in (mk1 (FStar_Syntax_Syntax.Comp (ct1))))
end)))
and elim_delayed_subst_meta : FStar_Syntax_Syntax.metadata  ->  FStar_Syntax_Syntax.metadata = (fun uu___277_25810 -> (match (uu___277_25810) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let uu____25824 = (FStar_List.map elim_delayed_subst_args args)
in FStar_Syntax_Syntax.Meta_pattern (uu____25824))
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let uu____25863 = (

let uu____25870 = (elim_delayed_subst_term t)
in ((m), (uu____25870)))
in FStar_Syntax_Syntax.Meta_monadic (uu____25863))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t) -> begin
(

let uu____25882 = (

let uu____25891 = (elim_delayed_subst_term t)
in ((m1), (m2), (uu____25891)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____25882))
end
| m -> begin
m
end))
and elim_delayed_subst_args : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun args -> (FStar_List.map (fun uu____25924 -> (match (uu____25924) with
| (t, q) -> begin
(

let uu____25943 = (elim_delayed_subst_term t)
in ((uu____25943), (q)))
end)) args))
and elim_delayed_subst_binders : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun bs -> (FStar_List.map (fun uu____25971 -> (match (uu____25971) with
| (x, q) -> begin
(

let uu____25990 = (

let uu___365_25991 = x
in (

let uu____25992 = (elim_delayed_subst_term x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___365_25991.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___365_25991.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____25992}))
in ((uu____25990), (q)))
end)) bs))


let elim_uvars_aux_tc : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.comp) FStar_Util.either  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either) = (fun env univ_names binders tc -> (

let t = (match (((binders), (tc))) with
| ([], FStar_Util.Inl (t)) -> begin
t
end
| ([], FStar_Util.Inr (c)) -> begin
(failwith "Impossible: empty bindes with a comp")
end
| (uu____26098, FStar_Util.Inr (c)) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
end
| (uu____26130, FStar_Util.Inl (t)) -> begin
(

let uu____26152 = (

let uu____26159 = (

let uu____26160 = (

let uu____26175 = (FStar_Syntax_Syntax.mk_Total t)
in ((binders), (uu____26175)))
in FStar_Syntax_Syntax.Tm_arrow (uu____26160))
in (FStar_Syntax_Syntax.mk uu____26159))
in (uu____26152 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end)
in (

let uu____26191 = (FStar_Syntax_Subst.open_univ_vars univ_names t)
in (match (uu____26191) with
| (univ_names1, t1) -> begin
(

let t2 = (remove_uvar_solutions env t1)
in (

let t3 = (FStar_Syntax_Subst.close_univ_vars univ_names1 t2)
in (

let t4 = (elim_delayed_subst_term t3)
in (

let uu____26223 = (match (binders) with
| [] -> begin
(([]), (FStar_Util.Inl (t4)))
end
| uu____26296 -> begin
(

let uu____26297 = (

let uu____26306 = (

let uu____26307 = (FStar_Syntax_Subst.compress t4)
in uu____26307.FStar_Syntax_Syntax.n)
in ((uu____26306), (tc)))
in (match (uu____26297) with
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inr (uu____26336)) -> begin
((binders1), (FStar_Util.Inr (c)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inl (uu____26383)) -> begin
((binders1), (FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))))
end
| (uu____26428, FStar_Util.Inl (uu____26429)) -> begin
(([]), (FStar_Util.Inl (t4)))
end
| uu____26460 -> begin
(failwith "Impossible")
end))
end)
in (match (uu____26223) with
| (binders1, tc1) -> begin
((univ_names1), (binders1), (tc1))
end)))))
end))))


let elim_uvars_aux_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun env univ_names binders t -> (

let uu____26597 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl (t)))
in (match (uu____26597) with
| (univ_names1, binders1, tc) -> begin
(

let uu____26671 = (FStar_Util.left tc)
in ((univ_names1), (binders1), (uu____26671)))
end)))


let elim_uvars_aux_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) = (fun env univ_names binders c -> (

let uu____26724 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr (c)))
in (match (uu____26724) with
| (univ_names1, binders1, tc) -> begin
(

let uu____26798 = (FStar_Util.right tc)
in ((univ_names1), (binders1), (uu____26798)))
end)))


let rec elim_uvars : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, lids, lids') -> begin
(

let uu____26839 = (elim_uvars_aux_t env univ_names binders typ)
in (match (uu____26839) with
| (univ_names1, binders1, typ1) -> begin
(

let uu___366_26879 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univ_names1), (binders1), (typ1), (lids), (lids'))); FStar_Syntax_Syntax.sigrng = uu___366_26879.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___366_26879.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___366_26879.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___366_26879.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uu___367_26894 = s
in (

let uu____26895 = (

let uu____26896 = (

let uu____26905 = (FStar_List.map (elim_uvars env) sigs)
in ((uu____26905), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____26896))
in {FStar_Syntax_Syntax.sigel = uu____26895; FStar_Syntax_Syntax.sigrng = uu___367_26894.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___367_26894.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___367_26894.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___367_26894.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univ_names, typ, lident, i, lids) -> begin
(

let uu____26922 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____26922) with
| (univ_names1, uu____26946, typ1) -> begin
(

let uu___368_26968 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univ_names1), (typ1), (lident), (i), (lids))); FStar_Syntax_Syntax.sigrng = uu___368_26968.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___368_26968.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___368_26968.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___368_26968.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) -> begin
(

let uu____26974 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____26974) with
| (univ_names1, uu____26998, typ1) -> begin
(

let uu___369_27020 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (univ_names1), (typ1))); FStar_Syntax_Syntax.sigrng = uu___369_27020.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___369_27020.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___369_27020.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___369_27020.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____27048 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____27048) with
| (opening, lbunivs) -> begin
(

let elim = (fun t -> (

let uu____27073 = (

let uu____27074 = (

let uu____27075 = (FStar_Syntax_Subst.subst opening t)
in (remove_uvar_solutions env uu____27075))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____27074))
in (elim_delayed_subst_term uu____27073)))
in (

let lbtyp = (elim lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (elim lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___370_27078 = lb
in {FStar_Syntax_Syntax.lbname = uu___370_27078.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___370_27078.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___370_27078.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___370_27078.FStar_Syntax_Syntax.lbpos}))))
end)))))
in (

let uu___371_27079 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((b), (lbs1))), (lids))); FStar_Syntax_Syntax.sigrng = uu___371_27079.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___371_27079.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___371_27079.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___371_27079.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(

let uu___372_27085 = s
in (

let uu____27086 = (

let uu____27087 = (remove_uvar_solutions env t)
in FStar_Syntax_Syntax.Sig_main (uu____27087))
in {FStar_Syntax_Syntax.sigel = uu____27086; FStar_Syntax_Syntax.sigrng = uu___372_27085.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___372_27085.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___372_27085.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___372_27085.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, t) -> begin
(

let uu____27091 = (elim_uvars_aux_t env us [] t)
in (match (uu____27091) with
| (us1, uu____27115, t1) -> begin
(

let uu___373_27137 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((l), (us1), (t1))); FStar_Syntax_Syntax.sigrng = uu___373_27137.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___373_27137.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___373_27137.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___373_27137.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____27138) -> begin
(failwith "Impossible: should have been desugared already")
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____27140 = (elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____27140) with
| (univs1, binders, signature) -> begin
(

let uu____27180 = (

let uu____27185 = (FStar_Syntax_Subst.univ_var_opening univs1)
in (match (uu____27185) with
| (univs_opening, univs2) -> begin
(

let uu____27208 = (FStar_Syntax_Subst.univ_var_closing univs2)
in ((univs_opening), (uu____27208)))
end))
in (match (uu____27180) with
| (univs_opening, univs_closing) -> begin
(

let uu____27211 = (

let binders1 = (FStar_Syntax_Subst.open_binders binders)
in (

let uu____27217 = (FStar_Syntax_Subst.opening_of_binders binders1)
in (

let uu____27218 = (FStar_Syntax_Subst.closing_of_binders binders1)
in ((uu____27217), (uu____27218)))))
in (match (uu____27211) with
| (b_opening, b_closing) -> begin
(

let n1 = (FStar_List.length univs1)
in (

let n_binders = (FStar_List.length binders)
in (

let elim_tscheme = (fun uu____27244 -> (match (uu____27244) with
| (us, t) -> begin
(

let n_us = (FStar_List.length us)
in (

let uu____27262 = (FStar_Syntax_Subst.open_univ_vars us t)
in (match (uu____27262) with
| (us1, t1) -> begin
(

let uu____27273 = (

let uu____27282 = (FStar_All.pipe_right b_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____27293 = (FStar_All.pipe_right b_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____27282), (uu____27293))))
in (match (uu____27273) with
| (b_opening1, b_closing1) -> begin
(

let uu____27322 = (

let uu____27331 = (FStar_All.pipe_right univs_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____27342 = (FStar_All.pipe_right univs_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____27331), (uu____27342))))
in (match (uu____27322) with
| (univs_opening1, univs_closing1) -> begin
(

let t2 = (

let uu____27372 = (FStar_Syntax_Subst.subst b_opening1 t1)
in (FStar_Syntax_Subst.subst univs_opening1 uu____27372))
in (

let uu____27373 = (elim_uvars_aux_t env [] [] t2)
in (match (uu____27373) with
| (uu____27400, uu____27401, t3) -> begin
(

let t4 = (

let uu____27424 = (

let uu____27425 = (FStar_Syntax_Subst.close_univ_vars us1 t3)
in (FStar_Syntax_Subst.subst b_closing1 uu____27425))
in (FStar_Syntax_Subst.subst univs_closing1 uu____27424))
in ((us1), (t4)))
end)))
end))
end))
end)))
end))
in (

let elim_term = (fun t -> (

let uu____27434 = (elim_uvars_aux_t env univs1 binders t)
in (match (uu____27434) with
| (uu____27453, uu____27454, t1) -> begin
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
| uu____27530 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((a.FStar_Syntax_Syntax.action_params), (body), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
end))
in (

let destruct_action_body = (fun body -> (

let uu____27557 = (

let uu____27558 = (FStar_Syntax_Subst.compress body)
in uu____27558.FStar_Syntax_Syntax.n)
in (match (uu____27557) with
| FStar_Syntax_Syntax.Tm_ascribed (defn, (FStar_Util.Inl (typ), FStar_Pervasives_Native.None), FStar_Pervasives_Native.None) -> begin
((defn), (typ))
end
| uu____27617 -> begin
(failwith "Impossible")
end)))
in (

let destruct_action_typ_templ = (fun t -> (

let uu____27650 = (

let uu____27651 = (FStar_Syntax_Subst.compress t)
in uu____27651.FStar_Syntax_Syntax.n)
in (match (uu____27650) with
| FStar_Syntax_Syntax.Tm_abs (pars, body, uu____27674) -> begin
(

let uu____27699 = (destruct_action_body body)
in (match (uu____27699) with
| (defn, typ) -> begin
((pars), (defn), (typ))
end))
end
| uu____27748 -> begin
(

let uu____27749 = (destruct_action_body t)
in (match (uu____27749) with
| (defn, typ) -> begin
(([]), (defn), (typ))
end))
end)))
in (

let uu____27804 = (elim_tscheme ((a.FStar_Syntax_Syntax.action_univs), (action_typ_templ)))
in (match (uu____27804) with
| (action_univs, t) -> begin
(

let uu____27813 = (destruct_action_typ_templ t)
in (match (uu____27813) with
| (action_params, action_defn, action_typ) -> begin
(

let a' = (

let uu___374_27860 = a
in {FStar_Syntax_Syntax.action_name = uu___374_27860.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___374_27860.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action_univs; FStar_Syntax_Syntax.action_params = action_params; FStar_Syntax_Syntax.action_defn = action_defn; FStar_Syntax_Syntax.action_typ = action_typ})
in a')
end))
end))))))
in (

let ed1 = (

let uu___375_27862 = ed
in (

let uu____27863 = (elim_tscheme ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____27864 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____27865 = (elim_tscheme ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____27866 = (elim_tscheme ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____27867 = (elim_tscheme ed.FStar_Syntax_Syntax.stronger)
in (

let uu____27868 = (elim_tscheme ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____27869 = (elim_tscheme ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____27870 = (elim_tscheme ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____27871 = (elim_tscheme ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____27872 = (elim_tscheme ed.FStar_Syntax_Syntax.trivial)
in (

let uu____27873 = (elim_term ed.FStar_Syntax_Syntax.repr)
in (

let uu____27874 = (elim_tscheme ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____27875 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____27876 = (FStar_List.map elim_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___375_27862.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___375_27862.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu____27863; FStar_Syntax_Syntax.bind_wp = uu____27864; FStar_Syntax_Syntax.if_then_else = uu____27865; FStar_Syntax_Syntax.ite_wp = uu____27866; FStar_Syntax_Syntax.stronger = uu____27867; FStar_Syntax_Syntax.close_wp = uu____27868; FStar_Syntax_Syntax.assert_p = uu____27869; FStar_Syntax_Syntax.assume_p = uu____27870; FStar_Syntax_Syntax.null_wp = uu____27871; FStar_Syntax_Syntax.trivial = uu____27872; FStar_Syntax_Syntax.repr = uu____27873; FStar_Syntax_Syntax.return_repr = uu____27874; FStar_Syntax_Syntax.bind_repr = uu____27875; FStar_Syntax_Syntax.actions = uu____27876; FStar_Syntax_Syntax.eff_attrs = uu___375_27862.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in (

let uu___376_27879 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ed1); FStar_Syntax_Syntax.sigrng = uu___376_27879.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___376_27879.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___376_27879.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___376_27879.FStar_Syntax_Syntax.sigattrs})))))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub_eff) -> begin
(

let elim_tscheme_opt = (fun uu___278_27900 -> (match (uu___278_27900) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (us, t) -> begin
(

let uu____27931 = (elim_uvars_aux_t env us [] t)
in (match (uu____27931) with
| (us1, uu____27963, t1) -> begin
FStar_Pervasives_Native.Some (((us1), (t1)))
end))
end))
in (

let sub_eff1 = (

let uu___377_27994 = sub_eff
in (

let uu____27995 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp)
in (

let uu____27998 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift)
in {FStar_Syntax_Syntax.source = uu___377_27994.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___377_27994.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = uu____27995; FStar_Syntax_Syntax.lift = uu____27998})))
in (

let uu___378_28001 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub_eff1); FStar_Syntax_Syntax.sigrng = uu___378_28001.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___378_28001.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___378_28001.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___378_28001.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univ_names, binders, comp, flags1) -> begin
(

let uu____28011 = (elim_uvars_aux_c env univ_names binders comp)
in (match (uu____28011) with
| (univ_names1, binders1, comp1) -> begin
(

let uu___379_28051 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (univ_names1), (binders1), (comp1), (flags1))); FStar_Syntax_Syntax.sigrng = uu___379_28051.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___379_28051.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___379_28051.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___379_28051.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_pragma (uu____28054) -> begin
s
end
| FStar_Syntax_Syntax.Sig_splice (uu____28055) -> begin
s
end))


let erase_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env t))


let unfold_head_once : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env t -> (

let aux = (fun f us args -> (

let uu____28102 = (FStar_TypeChecker_Env.lookup_nonrec_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]) env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____28102) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (head_def_ts) -> begin
(

let uu____28124 = (FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us)
in (match (uu____28124) with
| (uu____28131, head_def) -> begin
(

let t' = (FStar_Syntax_Syntax.mk_Tm_app head_def args FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let t'1 = (normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::[]) env t')
in FStar_Pervasives_Native.Some (t'1)))
end))
end)))
in (

let uu____28137 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____28137) with
| (head1, args) -> begin
(

let uu____28182 = (

let uu____28183 = (FStar_Syntax_Subst.compress head1)
in uu____28183.FStar_Syntax_Syntax.n)
in (match (uu____28182) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(aux fv [] args)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____28190; FStar_Syntax_Syntax.vars = uu____28191}, us) -> begin
(aux fv us args)
end
| uu____28197 -> begin
FStar_Pervasives_Native.None
end))
end))))




