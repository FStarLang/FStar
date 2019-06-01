
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


let rec env_to_string : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list  ->  Prims.string = (fun env -> (

let uu____1034 = (FStar_List.map (fun uu____1050 -> (match (uu____1050) with
| (bopt, c) -> begin
(

let uu____1064 = (match (bopt) with
| FStar_Pervasives_Native.None -> begin
"."
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.binder_to_string x)
end)
in (

let uu____1069 = (closure_to_string c)
in (FStar_Util.format2 "(%s, %s)" uu____1064 uu____1069)))
end)) env)
in (FStar_All.pipe_right uu____1034 (FStar_String.concat "; "))))
and closure_to_string : closure  ->  Prims.string = (fun uu___1_1077 -> (match (uu___1_1077) with
| Clos (env, t, uu____1081, uu____1082) -> begin
(

let uu____1129 = (FStar_All.pipe_right (FStar_List.length env) FStar_Util.string_of_int)
in (

let uu____1139 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "(env=%s elts; %s)" uu____1129 uu____1139)))
end
| Univ (uu____1142) -> begin
"Univ"
end
| Dummy -> begin
"dummy"
end))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun uu___2_1151 -> (match (uu___2_1151) with
| Arg (c, uu____1154, uu____1155) -> begin
(

let uu____1156 = (closure_to_string c)
in (FStar_Util.format1 "Closure %s" uu____1156))
end
| MemoLazy (uu____1159) -> begin
"MemoLazy"
end
| Abs (uu____1167, bs, uu____1169, uu____1170, uu____1171) -> begin
(

let uu____1176 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" uu____1176))
end
| UnivArgs (uu____1187) -> begin
"UnivArgs"
end
| Match (uu____1195) -> begin
"Match"
end
| App (uu____1205, t, uu____1207, uu____1208) -> begin
(

let uu____1209 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "App %s" uu____1209))
end
| Meta (uu____1212, m, uu____1214) -> begin
"Meta"
end
| Let (uu____1216) -> begin
"Let"
end
| Cfg (uu____1226) -> begin
"Cfg"
end
| Debug (t, uu____1229) -> begin
(

let uu____1230 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Debug %s" uu____1230))
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (

let uu____1244 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right uu____1244 (FStar_String.concat "; "))))


let is_empty : 'Auu____1259 . 'Auu____1259 Prims.list  ->  Prims.bool = (fun uu___3_1267 -> (match (uu___3_1267) with
| [] -> begin
true
end
| uu____1271 -> begin
false
end))


let lookup_bvar : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.bv  ->  closure = (fun env x -> (FStar_All.try_with (fun uu___115_1304 -> (match (()) with
| () -> begin
(

let uu____1305 = (FStar_List.nth env x.FStar_Syntax_Syntax.index)
in (FStar_Pervasives_Native.snd uu____1305))
end)) (fun uu___114_1322 -> (

let uu____1323 = (

let uu____1325 = (FStar_Syntax_Print.db_to_string x)
in (

let uu____1327 = (env_to_string env)
in (FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1325 uu____1327)))
in (failwith uu____1323)))))


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun l -> (

let uu____1338 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid)
in (match (uu____1338) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Pure_lid)
end
| uu____1343 -> begin
(

let uu____1345 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid)
in (match (uu____1345) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Tot_lid)
end
| uu____1350 -> begin
(

let uu____1352 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid)
in (match (uu____1352) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_PURE_lid)
end
| uu____1357 -> begin
FStar_Pervasives_Native.None
end))
end))
end)))


let norm_universe : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us1 = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let uu____1390 = (FStar_List.fold_left (fun uu____1416 u1 -> (match (uu____1416) with
| (cur_kernel, cur_max, out) -> begin
(

let uu____1441 = (FStar_Syntax_Util.univ_kernel u1)
in (match (uu____1441) with
| (k_u, n1) -> begin
(

let uu____1459 = (FStar_Syntax_Util.eq_univs cur_kernel k_u)
in (match (uu____1459) with
| true -> begin
((cur_kernel), (u1), (out))
end
| uu____1472 -> begin
((k_u), (u1), ((cur_max)::out))
end))
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us1)
in (match (uu____1390) with
| (uu____1480, u1, out) -> begin
(FStar_List.rev ((u1)::out))
end))))
in (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(FStar_All.try_with (fun uu___149_1506 -> (match (()) with
| () -> begin
(

let uu____1509 = (

let uu____1510 = (FStar_List.nth env x)
in (FStar_Pervasives_Native.snd uu____1510))
in (match (uu____1509) with
| Univ (u3) -> begin
((

let uu____1529 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv) (FStar_Options.Other ("univ_norm")))
in (match (uu____1529) with
| true -> begin
(

let uu____1534 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.print1 "Univ (in norm_universe): %s\n" uu____1534))
end
| uu____1537 -> begin
()
end));
(aux u3);
)
end
| Dummy -> begin
(u2)::[]
end
| uu____1539 -> begin
(

let uu____1540 = (

let uu____1542 = (FStar_Util.string_of_int x)
in (FStar_Util.format1 "Impossible: universe variable u@%s bound to a term" uu____1542))
in (failwith uu____1540))
end))
end)) (fun uu___148_1549 -> (match (uu___148_1549) with
| uu____1552 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.allow_unbound_universes) with
| true -> begin
(FStar_Syntax_Syntax.U_unknown)::[]
end
| uu____1556 -> begin
(

let uu____1558 = (

let uu____1560 = (FStar_Util.string_of_int x)
in (FStar_String.op_Hat "Universe variable not found: u@" uu____1560))
in (failwith uu____1558))
end)
end)))
end
| FStar_Syntax_Syntax.U_unif (uu____1565) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_zero -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_unif (uu____1574) -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_name (uu____1583) -> begin
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

let uu____1590 = (FStar_List.collect aux us)
in (FStar_All.pipe_right uu____1590 norm_univs))
in (match (us1) with
| (u_k)::(hd1)::rest -> begin
(

let rest1 = (hd1)::rest
in (

let uu____1607 = (FStar_Syntax_Util.univ_kernel u_k)
in (match (uu____1607) with
| (FStar_Syntax_Syntax.U_zero, n1) -> begin
(

let uu____1618 = (FStar_All.pipe_right rest1 (FStar_List.for_all (fun u3 -> (

let uu____1628 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____1628) with
| (uu____1635, m) -> begin
(n1 <= m)
end)))))
in (match (uu____1618) with
| true -> begin
rest1
end
| uu____1642 -> begin
us1
end))
end
| uu____1644 -> begin
us1
end)))
end
| uu____1650 -> begin
us1
end))
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1654 = (aux u3)
in (FStar_List.map (fun _1657 -> FStar_Syntax_Syntax.U_succ (_1657)) uu____1654))
end)))
in (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.erase_universes) with
| true -> begin
FStar_Syntax_Syntax.U_unknown
end
| uu____1659 -> begin
(

let uu____1661 = (aux u)
in (match (uu____1661) with
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


let rec inline_closure_env : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env stack t -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____1830 -> (

let uu____1831 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1833 = (env_to_string env)
in (

let uu____1835 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n" uu____1831 uu____1833 uu____1835))))));
(match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars) -> begin
(rebuild_closure cfg env stack t)
end
| uu____1848 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1851) -> begin
(

let uu____1874 = (FStar_Syntax_Subst.compress t)
in (inline_closure_env cfg env stack uu____1874))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1875) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_name (uu____1876) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_lazy (uu____1877) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1878) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_uvar (uv, s) -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____1903) -> begin
(

let uu____1916 = (

let uu____1918 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____1920 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s): CheckNoUvars: Unexpected unification variable remains: %s" uu____1918 uu____1920)))
in (failwith uu____1916))
end
| uu____1925 -> begin
(inline_closure_env cfg env stack t1)
end))
end
| uu____1926 -> begin
(

let s' = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (fun s1 -> (FStar_All.pipe_right s1 (FStar_List.map (fun uu___4_1961 -> (match (uu___4_1961) with
| FStar_Syntax_Syntax.NT (x, t1) -> begin
(

let uu____1968 = (

let uu____1975 = (inline_closure_env cfg env [] t1)
in ((x), (uu____1975)))
in FStar_Syntax_Syntax.NT (uu____1968))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let x_i = (FStar_Syntax_Syntax.bv_to_tm (

let uu___243_1987 = x
in {FStar_Syntax_Syntax.ppname = uu___243_1987.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___243_1987.FStar_Syntax_Syntax.sort}))
in (

let t1 = (inline_closure_env cfg env [] x_i)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x_j) -> begin
FStar_Syntax_Syntax.NM (((x), (x_j.FStar_Syntax_Syntax.index)))
end
| uu____1993 -> begin
FStar_Syntax_Syntax.NT (((x), (t1)))
end)))
end
| uu____1996 -> begin
(failwith "Impossible: subst invariant of uvar nodes")
end)))))))
in (

let t1 = (

let uu___252_2001 = t
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (((uv), (((s'), ((FStar_Pervasives_Native.snd s)))))); FStar_Syntax_Syntax.pos = uu___252_2001.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___252_2001.FStar_Syntax_Syntax.vars})
in (rebuild_closure cfg env stack t1)))
end)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let t1 = (

let uu____2022 = (

let uu____2023 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (uu____2023))
in (mk uu____2022 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env stack t1))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let t1 = (

let uu____2031 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2031))
in (rebuild_closure cfg env stack t1))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____2033 = (lookup_bvar env x)
in (match (uu____2033) with
| Univ (uu____2036) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(

let x1 = (

let uu___268_2041 = x
in {FStar_Syntax_Syntax.ppname = uu___268_2041.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___268_2041.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun})
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_bvar (x1)) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env stack t1)))
end
| Clos (env1, t0, uu____2047, uu____2048) -> begin
(inline_closure_env cfg env1 stack t0)
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____2139 stack1 -> (match (uu____2139) with
| (a, aq) -> begin
(

let uu____2151 = (

let uu____2152 = (

let uu____2159 = (

let uu____2160 = (

let uu____2192 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____2192), (false)))
in Clos (uu____2160))
in ((uu____2159), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (uu____2152))
in (uu____2151)::stack1)
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

let uu____2360 = (close_binders cfg env bs)
in (match (uu____2360) with
| (bs1, env') -> begin
(

let c1 = (close_comp cfg env' c)
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_arrow (((bs1), (c1)))) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env stack t1)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____2410) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.for_extraction -> begin
(inline_closure_env cfg env stack x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____2421 = (

let uu____2434 = (

let uu____2443 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2443)::[])
in (close_binders cfg env uu____2434))
in (match (uu____2421) with
| (x1, env1) -> begin
(

let phi1 = (non_tail_inline_closure_env cfg env1 phi)
in (

let t1 = (

let uu____2488 = (

let uu____2489 = (

let uu____2496 = (

let uu____2497 = (FStar_List.hd x1)
in (FStar_All.pipe_right uu____2497 FStar_Pervasives_Native.fst))
in ((uu____2496), (phi1)))
in FStar_Syntax_Syntax.Tm_refine (uu____2489))
in (mk uu____2488 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env1 stack t1)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, (annot, tacopt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____2596 = (non_tail_inline_closure_env cfg env t2)
in FStar_Util.Inl (uu____2596))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2610 = (close_comp cfg env c)
in FStar_Util.Inr (uu____2610))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (non_tail_inline_closure_env cfg env))
in (

let t2 = (

let uu____2629 = (

let uu____2630 = (

let uu____2657 = (non_tail_inline_closure_env cfg env t1)
in ((uu____2657), (((annot1), (tacopt1))), (lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2630))
in (mk uu____2629 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env stack t2))))
end
| FStar_Syntax_Syntax.Tm_quoted (t', qi) -> begin
(

let t1 = (match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____2703 = (

let uu____2704 = (

let uu____2711 = (non_tail_inline_closure_env cfg env t')
in ((uu____2711), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____2704))
in (mk uu____2703 t.FStar_Syntax_Syntax.pos))
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

let env1 = (FStar_List.fold_left (fun env1 uu____2766 -> (dummy)::env1) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (non_tail_inline_closure_env cfg env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (non_tail_inline_closure_env cfg env1 lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____2787 = (

let uu____2798 = (FStar_Syntax_Syntax.is_top_level ((lb)::[]))
in (match (uu____2798) with
| true -> begin
((lb.FStar_Syntax_Syntax.lbname), (body))
end
| uu____2817 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2820 = (non_tail_inline_closure_env cfg ((dummy)::env0) body)
in ((FStar_Util.Inl ((

let uu___360_2836 = x
in {FStar_Syntax_Syntax.ppname = uu___360_2836.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___360_2836.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = typ}))), (uu____2820))))
end))
in (match (uu____2787) with
| (nm, body1) -> begin
(

let lb1 = (

let uu___365_2854 = lb
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___365_2854.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = uu___365_2854.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___365_2854.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___365_2854.FStar_Syntax_Syntax.lbpos})
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (body1)))) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env0 stack t1)))
end))))))
end
| FStar_Syntax_Syntax.Tm_let ((uu____2871, lbs), body) -> begin
(

let norm_one_lb = (fun env1 lb -> (

let env_univs = (FStar_List.fold_right (fun uu____2937 env2 -> (dummy)::env2) lb.FStar_Syntax_Syntax.lbunivs env1)
in (

let env2 = (

let uu____2954 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____2954) with
| true -> begin
env_univs
end
| uu____2957 -> begin
(FStar_List.fold_right (fun uu____2969 env2 -> (dummy)::env2) lbs env_univs)
end))
in (

let ty = (non_tail_inline_closure_env cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (

let nm = (

let uu____2993 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____2993) with
| true -> begin
lb.FStar_Syntax_Syntax.lbname
end
| uu____3000 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in FStar_Util.Inl ((

let uu___388_3004 = x
in {FStar_Syntax_Syntax.ppname = uu___388_3004.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___388_3004.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
end))
in (

let uu___391_3005 = lb
in (

let uu____3006 = (non_tail_inline_closure_env cfg env2 lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___391_3005.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___391_3005.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____3006; FStar_Syntax_Syntax.lbattrs = uu___391_3005.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___391_3005.FStar_Syntax_Syntax.lbpos})))))))
in (

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body1 = (

let body_env = (FStar_List.fold_right (fun uu____3038 env1 -> (dummy)::env1) lbs1 env)
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
and rebuild_closure : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env stack t -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____3130 -> (

let uu____3131 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____3133 = (env_to_string env)
in (

let uu____3135 = (stack_to_string stack)
in (

let uu____3137 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print4 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n" uu____3131 uu____3133 uu____3135 uu____3137)))))));
(match (stack) with
| [] -> begin
t
end
| (Arg (Clos (env_arg, tm, uu____3144, uu____3145), aq, r))::stack1 -> begin
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

let uu____3226 = (close_binders cfg env' bs)
in (match (uu____3226) with
| (bs1, uu____3242) -> begin
(

let lopt1 = (close_lcomp_opt cfg env'' lopt)
in (

let uu____3262 = (

let uu___449_3265 = (FStar_Syntax_Util.abs bs1 t lopt1)
in {FStar_Syntax_Syntax.n = uu___449_3265.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___449_3265.FStar_Syntax_Syntax.vars})
in (rebuild_closure cfg env stack1 uu____3262)))
end))
end
| (Match (env1, branches, cfg1, r))::stack1 -> begin
(

let close_one_branch = (fun env2 uu____3321 -> (match (uu____3321) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env3 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____3436) -> begin
((p), (env3))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3467 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____3556 uu____3557 -> (match (((uu____3556), (uu____3557))) with
| ((pats1, env4), (p1, b)) -> begin
(

let uu____3707 = (norm_pat env4 p1)
in (match (uu____3707) with
| (p2, env5) -> begin
(((((p2), (b)))::pats1), (env5))
end))
end)) (([]), (env3))))
in (match (uu____3467) with
| (pats1, env4) -> begin
(((

let uu___486_3877 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___486_3877.FStar_Syntax_Syntax.p})), (env4))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___490_3898 = x
in (

let uu____3899 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___490_3898.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___490_3898.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3899}))
in (((

let uu___493_3913 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___493_3913.FStar_Syntax_Syntax.p})), ((dummy)::env3)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___497_3924 = x
in (

let uu____3925 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___497_3924.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___497_3924.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3925}))
in (((

let uu___500_3939 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___500_3939.FStar_Syntax_Syntax.p})), ((dummy)::env3)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t1) -> begin
(

let x1 = (

let uu___506_3955 = x
in (

let uu____3956 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___506_3955.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___506_3955.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3956}))
in (

let t2 = (non_tail_inline_closure_env cfg1 env3 t1)
in (((

let uu___510_3973 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t2))); FStar_Syntax_Syntax.p = uu___510_3973.FStar_Syntax_Syntax.p})), (env3))))
end))
in (

let uu____3978 = (norm_pat env2 pat)
in (match (uu____3978) with
| (pat1, env3) -> begin
(

let w_opt1 = (match (w_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____4047 = (non_tail_inline_closure_env cfg1 env3 w)
in FStar_Pervasives_Native.Some (uu____4047))
end)
in (

let tm1 = (non_tail_inline_closure_env cfg1 env3 tm)
in ((pat1), (w_opt1), (tm1))))
end)))
end))
in (

let t1 = (

let uu____4066 = (

let uu____4067 = (

let uu____4090 = (FStar_All.pipe_right branches (FStar_List.map (close_one_branch env1)))
in ((t), (uu____4090)))
in FStar_Syntax_Syntax.Tm_match (uu____4067))
in (mk uu____4066 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg1 env1 stack1 t1)))
end
| (Meta (env_m, m, r))::stack1 -> begin
(

let m1 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (names1, args) -> begin
(

let uu____4226 = (

let uu____4247 = (FStar_All.pipe_right names1 (FStar_List.map (non_tail_inline_closure_env cfg env_m)))
in (

let uu____4264 = (FStar_All.pipe_right args (FStar_List.map (fun args1 -> (FStar_All.pipe_right args1 (FStar_List.map (fun uu____4373 -> (match (uu____4373) with
| (a, q) -> begin
(

let uu____4400 = (non_tail_inline_closure_env cfg env_m a)
in ((uu____4400), (q)))
end)))))))
in ((uu____4247), (uu____4264))))
in FStar_Syntax_Syntax.Meta_pattern (uu____4226))
end
| FStar_Syntax_Syntax.Meta_monadic (m1, tbody) -> begin
(

let uu____4429 = (

let uu____4436 = (non_tail_inline_closure_env cfg env_m tbody)
in ((m1), (uu____4436)))
in FStar_Syntax_Syntax.Meta_monadic (uu____4429))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody) -> begin
(

let uu____4448 = (

let uu____4457 = (non_tail_inline_closure_env cfg env_m tbody)
in ((m1), (m2), (uu____4457)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____4448))
end
| uu____4462 -> begin
m
end)
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m1)))) r)
in (rebuild_closure cfg env stack1 t1)))
end
| uu____4468 -> begin
(failwith "Impossible: unexpected stack element")
end);
))
and close_imp : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun cfg env imp -> (match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____4484 = (

let uu____4485 = (inline_closure_env cfg env [] t)
in FStar_Syntax_Syntax.Meta (uu____4485))
in FStar_Pervasives_Native.Some (uu____4484))
end
| i -> begin
i
end))
and close_binders : FStar_TypeChecker_Cfg.cfg  ->  env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * env) = (fun cfg env bs -> (

let uu____4502 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____4586 uu____4587 -> (match (((uu____4586), (uu____4587))) with
| ((env1, out), (b, imp)) -> begin
(

let b1 = (

let uu___565_4727 = b
in (

let uu____4728 = (inline_closure_env cfg env1 [] b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___565_4727.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___565_4727.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4728}))
in (

let imp1 = (close_imp cfg env1 imp)
in (

let env2 = (dummy)::env1
in ((env2), ((((b1), (imp1)))::out)))))
end)) ((env), ([]))))
in (match (uu____4502) with
| (env1, bs1) -> begin
(((FStar_List.rev bs1)), (env1))
end)))
and close_comp : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars) -> begin
c
end
| uu____4870 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____4883 = (inline_closure_env cfg env [] t)
in (

let uu____4884 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____4883 uu____4884)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____4897 = (inline_closure_env cfg env [] t)
in (

let uu____4898 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____4897 uu____4898)))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let rt = (inline_closure_env cfg env [] c1.FStar_Syntax_Syntax.result_typ)
in (

let args = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun uu____4952 -> (match (uu____4952) with
| (a, q) -> begin
(

let uu____4973 = (inline_closure_env cfg env [] a)
in ((uu____4973), (q)))
end))))
in (

let flags = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___5_4990 -> (match (uu___5_4990) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____4994 = (inline_closure_env cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____4994))
end
| f -> begin
f
end))))
in (

let uu____4998 = (

let uu___598_4999 = c1
in (

let uu____5000 = (FStar_List.map (norm_universe cfg env) c1.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = uu____5000; FStar_Syntax_Syntax.effect_name = uu___598_4999.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp uu____4998)))))
end)
end))
and filter_out_lcomp_cflags : FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun flags -> (FStar_All.pipe_right flags (FStar_List.filter (fun uu___6_5010 -> (match (uu___6_5010) with
| FStar_Syntax_Syntax.DECREASES (uu____5012) -> begin
false
end
| uu____5016 -> begin
true
end)))))
and close_lcomp_opt : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.filter (fun uu___7_5035 -> (match (uu___7_5035) with
| FStar_Syntax_Syntax.DECREASES (uu____5037) -> begin
false
end
| uu____5041 -> begin
true
end))))
in (

let rc1 = (

let uu___615_5044 = rc
in (

let uu____5045 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inline_closure_env cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___615_5044.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____5045; FStar_Syntax_Syntax.residual_flags = flags}))
in FStar_Pervasives_Native.Some (rc1)))
end
| uu____5054 -> begin
lopt
end))


let closure_as_term : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (non_tail_inline_closure_env cfg env t))


let unembed_binder_knot : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let unembed_binder : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option = (fun t -> (

let uu____5102 = (FStar_ST.op_Bang unembed_binder_knot)
in (match (uu____5102) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____5141 = (FStar_Syntax_Embeddings.unembed e t)
in (uu____5141 true FStar_Syntax_Embeddings.id_norm_cb))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_UnembedBinderKnot), ("unembed_binder_knot is unset!")));
FStar_Pervasives_Native.None;
)
end)))


let mk_psc_subst : 'Auu____5161 . FStar_TypeChecker_Cfg.cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____5161) FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun cfg env -> (FStar_List.fold_right (fun uu____5223 subst1 -> (match (uu____5223) with
| (binder_opt, closure) -> begin
(match (((binder_opt), (closure))) with
| (FStar_Pervasives_Native.Some (b), Clos (env1, term, uu____5264, uu____5265)) -> begin
(

let uu____5326 = b
in (match (uu____5326) with
| (bv, uu____5334) -> begin
(

let uu____5335 = (

let uu____5337 = (FStar_Syntax_Util.is_constructed_typ bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.binder_lid)
in (not (uu____5337)))
in (match (uu____5335) with
| true -> begin
subst1
end
| uu____5342 -> begin
(

let term1 = (closure_as_term cfg env1 term)
in (

let uu____5345 = (unembed_binder term1)
in (match (uu____5345) with
| FStar_Pervasives_Native.None -> begin
subst1
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let b1 = (

let uu____5352 = (

let uu___650_5353 = bv
in (

let uu____5354 = (FStar_Syntax_Subst.subst subst1 (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___650_5353.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___650_5353.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5354}))
in (FStar_Syntax_Syntax.freshen_bv uu____5352))
in (

let b_for_x = (

let uu____5360 = (

let uu____5367 = (FStar_Syntax_Syntax.bv_to_name b1)
in (((FStar_Pervasives_Native.fst x)), (uu____5367)))
in FStar_Syntax_Syntax.NT (uu____5360))
in (

let subst2 = (FStar_List.filter (fun uu___8_5383 -> (match (uu___8_5383) with
| FStar_Syntax_Syntax.NT (uu____5385, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (b'); FStar_Syntax_Syntax.pos = uu____5387; FStar_Syntax_Syntax.vars = uu____5388}) -> begin
(

let uu____5393 = (FStar_Ident.ident_equals b1.FStar_Syntax_Syntax.ppname b'.FStar_Syntax_Syntax.ppname)
in (not (uu____5393)))
end
| uu____5395 -> begin
true
end)) subst1)
in (b_for_x)::subst2)))
end)))
end))
end))
end
| uu____5397 -> begin
subst1
end)
end)) env []))


let reduce_primops : 'Auu____5419 . FStar_Syntax_Embeddings.norm_cb  ->  FStar_TypeChecker_Cfg.cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____5419) FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun norm_cb cfg env tm -> (match ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.primops))) with
| true -> begin
tm
end
| uu____5469 -> begin
(

let uu____5471 = (FStar_Syntax_Util.head_and_args tm)
in (match (uu____5471) with
| (head1, args) -> begin
(

let uu____5516 = (

let uu____5517 = (FStar_Syntax_Util.un_uinst head1)
in uu____5517.FStar_Syntax_Syntax.n)
in (match (uu____5516) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5523 = (FStar_TypeChecker_Cfg.find_prim_step cfg fv)
in (match (uu____5523) with
| FStar_Pervasives_Native.Some (prim_step) when (prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok || (not (cfg.FStar_TypeChecker_Cfg.strong))) -> begin
(

let l = (FStar_List.length args)
in (match ((l < prim_step.FStar_TypeChecker_Cfg.arity)) with
| true -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5546 -> (

let uu____5547 = (FStar_Syntax_Print.lid_to_string prim_step.FStar_TypeChecker_Cfg.name)
in (

let uu____5549 = (FStar_Util.string_of_int l)
in (

let uu____5551 = (FStar_Util.string_of_int prim_step.FStar_TypeChecker_Cfg.arity)
in (FStar_Util.print3 "primop: found partially applied %s (%s/%s args)\n" uu____5547 uu____5549 uu____5551))))));
tm;
)
end
| uu____5554 -> begin
(

let uu____5556 = (match ((Prims.op_Equality l prim_step.FStar_TypeChecker_Cfg.arity)) with
| true -> begin
((args), ([]))
end
| uu____5605 -> begin
(FStar_List.splitAt prim_step.FStar_TypeChecker_Cfg.arity args)
end)
in (match (uu____5556) with
| (args_1, args_2) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5642 -> (

let uu____5643 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: trying to reduce <%s>\n" uu____5643))));
(

let psc = {FStar_TypeChecker_Cfg.psc_range = head1.FStar_Syntax_Syntax.pos; FStar_TypeChecker_Cfg.psc_subst = (fun uu____5648 -> (match (prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution) with
| true -> begin
(mk_psc_subst cfg env)
end
| uu____5650 -> begin
[]
end))}
in (

let r = (prim_step.FStar_TypeChecker_Cfg.interpretation psc norm_cb args_1)
in (match (r) with
| FStar_Pervasives_Native.None -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5662 -> (

let uu____5663 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: <%s> did not reduce\n" uu____5663))));
tm;
)
end
| FStar_Pervasives_Native.Some (reduced) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5671 -> (

let uu____5672 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____5674 = (FStar_Syntax_Print.term_to_string reduced)
in (FStar_Util.print2 "primop: <%s> reduced to <%s>\n" uu____5672 uu____5674)))));
(FStar_Syntax_Util.mk_app reduced args_2);
)
end)));
)
end))
end))
end
| FStar_Pervasives_Native.Some (uu____5677) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5681 -> (

let uu____5682 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: not reducing <%s> since we\'re doing strong reduction\n" uu____5682))));
tm;
)
end
| FStar_Pervasives_Native.None -> begin
tm
end))
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of) when (not (cfg.FStar_TypeChecker_Cfg.strong)) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5688 -> (

let uu____5689 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: reducing <%s>\n" uu____5689))));
(match (args) with
| ((a1, uu____5695))::[] -> begin
(FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range a1.FStar_Syntax_Syntax.pos tm.FStar_Syntax_Syntax.pos)
end
| uu____5720 -> begin
tm
end);
)
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of) when (not (cfg.FStar_TypeChecker_Cfg.strong)) -> begin
((FStar_TypeChecker_Cfg.log_primops cfg (fun uu____5734 -> (

let uu____5735 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: reducing <%s>\n" uu____5735))));
(match (args) with
| ((t, uu____5741))::((r, uu____5743))::[] -> begin
(

let uu____5784 = (FStar_TypeChecker_Cfg.try_unembed_simple FStar_Syntax_Embeddings.e_range r)
in (match (uu____5784) with
| FStar_Pervasives_Native.Some (rng) -> begin
(FStar_Syntax_Subst.set_use_range rng t)
end
| FStar_Pervasives_Native.None -> begin
tm
end))
end
| uu____5790 -> begin
tm
end);
)
end
| uu____5801 -> begin
tm
end))
end))
end))


let reduce_equality : 'Auu____5812 . FStar_Syntax_Embeddings.norm_cb  ->  FStar_TypeChecker_Cfg.cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____5812) FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun norm_cb cfg tm -> (reduce_primops norm_cb (

let uu___738_5861 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___740_5864 = FStar_TypeChecker_Cfg.default_steps
in {FStar_TypeChecker_Cfg.beta = uu___740_5864.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___740_5864.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___740_5864.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___740_5864.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___740_5864.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = true; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___740_5864.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___740_5864.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___740_5864.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___740_5864.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___740_5864.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___740_5864.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___740_5864.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___740_5864.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___740_5864.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___740_5864.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___740_5864.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___740_5864.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___740_5864.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___740_5864.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___740_5864.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___740_5864.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___740_5864.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___740_5864.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___740_5864.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___740_5864.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___738_5861.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___738_5861.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___738_5861.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = FStar_TypeChecker_Cfg.equality_ops; FStar_TypeChecker_Cfg.strong = uu___738_5861.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___738_5861.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___738_5861.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___738_5861.FStar_TypeChecker_Cfg.reifying}) tm))

type norm_request_t =
| Norm_request_none
| Norm_request_ready
| Norm_request_requires_rejig


let uu___is_Norm_request_none : norm_request_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Norm_request_none -> begin
true
end
| uu____5875 -> begin
false
end))


let uu___is_Norm_request_ready : norm_request_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Norm_request_ready -> begin
true
end
| uu____5886 -> begin
false
end))


let uu___is_Norm_request_requires_rejig : norm_request_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Norm_request_requires_rejig -> begin
true
end
| uu____5897 -> begin
false
end))


let is_norm_request : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  norm_request_t = (fun hd1 args -> (

let aux = (fun min_args -> (

let uu____5918 = (FStar_All.pipe_right args FStar_List.length)
in (FStar_All.pipe_right uu____5918 (fun n1 -> (match ((n1 < min_args)) with
| true -> begin
Norm_request_none
end
| uu____5944 -> begin
(match ((Prims.op_Equality n1 min_args)) with
| true -> begin
Norm_request_ready
end
| uu____5948 -> begin
Norm_request_requires_rejig
end)
end)))))
in (

let uu____5950 = (

let uu____5951 = (FStar_Syntax_Util.un_uinst hd1)
in uu____5951.FStar_Syntax_Syntax.n)
in (match (uu____5950) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term) -> begin
(aux (Prims.parse_int "2"))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize) -> begin
(aux (Prims.parse_int "1"))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm) -> begin
(aux (Prims.parse_int "3"))
end
| uu____5960 -> begin
Norm_request_none
end))))


let should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg  ->  Prims.bool = (fun cfg -> ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.no_full_norm)) && (

let uu____5969 = (FStar_Ident.lid_equals cfg.FStar_TypeChecker_Cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid)
in (not (uu____5969)))))


let rejig_norm_request : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term = (fun hd1 args -> (

let uu____5982 = (

let uu____5983 = (FStar_Syntax_Util.un_uinst hd1)
in uu____5983.FStar_Syntax_Syntax.n)
in (match (uu____5982) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term) -> begin
(match (args) with
| (t1)::(t2)::rest when ((FStar_List.length rest) > (Prims.parse_int "0")) -> begin
(

let uu____6041 = (FStar_Syntax_Util.mk_app hd1 ((t1)::(t2)::[]))
in (FStar_Syntax_Util.mk_app uu____6041 rest))
end
| uu____6068 -> begin
(failwith "Impossible! invalid rejig_norm_request for normalize_term")
end)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize) -> begin
(match (args) with
| (t)::rest when ((FStar_List.length rest) > (Prims.parse_int "0")) -> begin
(

let uu____6108 = (FStar_Syntax_Util.mk_app hd1 ((t)::[]))
in (FStar_Syntax_Util.mk_app uu____6108 rest))
end
| uu____6127 -> begin
(failwith "Impossible! invalid rejig_norm_request for normalize")
end)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm) -> begin
(match (args) with
| (t1)::(t2)::(t3)::rest when ((FStar_List.length rest) > (Prims.parse_int "0")) -> begin
(

let uu____6201 = (FStar_Syntax_Util.mk_app hd1 ((t1)::(t2)::(t3)::[]))
in (FStar_Syntax_Util.mk_app uu____6201 rest))
end
| uu____6236 -> begin
(failwith "Impossible! invalid rejig_norm_request for norm")
end)
end
| uu____6238 -> begin
(

let uu____6239 = (

let uu____6241 = (FStar_Syntax_Print.term_to_string hd1)
in (FStar_String.op_Hat "Impossible! invalid rejig_norm_request for: %s" uu____6241))
in (failwith uu____6239))
end)))


let is_nbe_request : FStar_TypeChecker_Env.step Prims.list  ->  Prims.bool = (fun s -> (FStar_Util.for_some (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s))


let tr_norm_step : FStar_Syntax_Embeddings.norm_step  ->  FStar_TypeChecker_Env.step Prims.list = (fun uu___9_6262 -> (match (uu___9_6262) with
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

let uu____6269 = (

let uu____6272 = (

let uu____6273 = (FStar_List.map FStar_Ident.lid_of_str names1)
in FStar_TypeChecker_Env.UnfoldOnly (uu____6273))
in (uu____6272)::[])
in (FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::uu____6269)
end
| FStar_Syntax_Embeddings.UnfoldFully (names1) -> begin
(

let uu____6281 = (

let uu____6284 = (

let uu____6285 = (FStar_List.map FStar_Ident.lid_of_str names1)
in FStar_TypeChecker_Env.UnfoldFully (uu____6285))
in (uu____6284)::[])
in (FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::uu____6281)
end
| FStar_Syntax_Embeddings.UnfoldAttr (names1) -> begin
(

let uu____6293 = (

let uu____6296 = (

let uu____6297 = (FStar_List.map FStar_Ident.lid_of_str names1)
in FStar_TypeChecker_Env.UnfoldAttr (uu____6297))
in (uu____6296)::[])
in (FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::uu____6293)
end
| FStar_Syntax_Embeddings.NBE -> begin
(FStar_TypeChecker_Env.NBE)::[]
end))


let tr_norm_steps : FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_TypeChecker_Env.step Prims.list = (fun s -> (FStar_List.concatMap tr_norm_step s))


let get_norm_request : 'Auu____6322 . FStar_TypeChecker_Cfg.cfg  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term * 'Auu____6322) Prims.list  ->  (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun cfg full_norm args -> (

let parse_steps = (fun s -> (

let uu____6373 = (

let uu____6378 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_norm_step)
in (FStar_TypeChecker_Cfg.try_unembed_simple uu____6378 s))
in (match (uu____6373) with
| FStar_Pervasives_Native.Some (steps) -> begin
(

let uu____6394 = (tr_norm_steps steps)
in FStar_Pervasives_Native.Some (uu____6394))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))
in (

let inherited_steps = (FStar_List.append (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.erase_universes) with
| true -> begin
(FStar_TypeChecker_Env.EraseUniverses)::[]
end
| uu____6409 -> begin
[]
end) (FStar_List.append (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.allow_unbound_universes) with
| true -> begin
(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]
end
| uu____6414 -> begin
[]
end) (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.nbe_step) with
| true -> begin
(FStar_TypeChecker_Env.NBE)::[]
end
| uu____6419 -> begin
[]
end)))
in (match (args) with
| (uu____6429)::((tm, uu____6431))::[] -> begin
(

let s = (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Reify)::[]
in FStar_Pervasives_Native.Some ((((FStar_List.append inherited_steps s)), (tm))))
end
| ((tm, uu____6460))::[] -> begin
(

let s = (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Reify)::[]
in FStar_Pervasives_Native.Some ((((FStar_List.append inherited_steps s)), (tm))))
end
| ((steps, uu____6481))::(uu____6482)::((tm, uu____6484))::[] -> begin
(

let add_exclude = (fun s z -> (

let uu____6522 = (FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s)
in (match (uu____6522) with
| true -> begin
s
end
| uu____6527 -> begin
(FStar_TypeChecker_Env.Exclude (z))::s
end)))
in (

let uu____6529 = (

let uu____6534 = (full_norm steps)
in (parse_steps uu____6534))
in (match (uu____6529) with
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
| uu____6573 -> begin
FStar_Pervasives_Native.None
end))))


let nbe_eval : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_Env.steps  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg s tm -> (

let delta_level = (

let uu____6605 = (FStar_All.pipe_right s (FStar_Util.for_some (fun uu___10_6612 -> (match (uu___10_6612) with
| FStar_TypeChecker_Env.UnfoldUntil (uu____6614) -> begin
true
end
| FStar_TypeChecker_Env.UnfoldOnly (uu____6616) -> begin
true
end
| FStar_TypeChecker_Env.UnfoldFully (uu____6620) -> begin
true
end
| uu____6624 -> begin
false
end))))
in (match (uu____6605) with
| true -> begin
(FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]
end
| uu____6629 -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end))
in ((FStar_TypeChecker_Cfg.log_nbe cfg (fun uu____6634 -> (

let uu____6635 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Invoking NBE with  %s\n" uu____6635))));
(

let tm_norm = (

let uu____6639 = (

let uu____6654 = (FStar_TypeChecker_Cfg.cfg_env cfg)
in uu____6654.FStar_TypeChecker_Env.nbe)
in (uu____6639 s cfg.FStar_TypeChecker_Cfg.tcenv tm))
in ((FStar_TypeChecker_Cfg.log_nbe cfg (fun uu____6658 -> (

let uu____6659 = (FStar_Syntax_Print.term_to_string tm_norm)
in (FStar_Util.print1 "Result of NBE is  %s\n" uu____6659))));
tm_norm;
));
)))


let is_reify_head : stack_elt Prims.list  ->  Prims.bool = (fun uu___11_6670 -> (match (uu___11_6670) with
| (App (uu____6674, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____6675; FStar_Syntax_Syntax.vars = uu____6676}, uu____6677, uu____6678))::uu____6679 -> begin
true
end
| uu____6685 -> begin
false
end))


let firstn : 'Auu____6696 . Prims.int  ->  'Auu____6696 Prims.list  ->  ('Auu____6696 Prims.list * 'Auu____6696 Prims.list) = (fun k l -> (match (((FStar_List.length l) < k)) with
| true -> begin
((l), ([]))
end
| uu____6726 -> begin
(FStar_Util.first_N k l)
end))


let should_reify : FStar_TypeChecker_Cfg.cfg  ->  stack_elt Prims.list  ->  Prims.bool = (fun cfg stack -> (

let rec drop_irrel = (fun uu___12_6753 -> (match (uu___12_6753) with
| (MemoLazy (uu____6758))::s -> begin
(drop_irrel s)
end
| (UnivArgs (uu____6768))::s -> begin
(drop_irrel s)
end
| s -> begin
s
end))
in (

let uu____6781 = (drop_irrel stack)
in (match (uu____6781) with
| (App (uu____6785, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____6786; FStar_Syntax_Syntax.vars = uu____6787}, uu____6788, uu____6789))::uu____6790 -> begin
cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.reify_
end
| uu____6795 -> begin
false
end))))


let rec maybe_weakly_reduced : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun tm -> (

let aux_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (t, uu____6824) -> begin
(maybe_weakly_reduced t)
end
| FStar_Syntax_Syntax.Total (t, uu____6834) -> begin
(maybe_weakly_reduced t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
((maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) || (FStar_Util.for_some (fun uu____6855 -> (match (uu____6855) with
| (a, uu____6866) -> begin
(maybe_weakly_reduced a)
end)) ct.FStar_Syntax_Syntax.effect_args))
end))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____6877) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (uu____6902) -> begin
false
end
| FStar_Syntax_Syntax.Tm_uvar (uu____6904) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____6918) -> begin
false
end
| FStar_Syntax_Syntax.Tm_bvar (uu____6920) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (uu____6922) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____6924) -> begin
false
end
| FStar_Syntax_Syntax.Tm_lazy (uu____6926) -> begin
false
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| FStar_Syntax_Syntax.Tm_uinst (uu____6929) -> begin
false
end
| FStar_Syntax_Syntax.Tm_quoted (uu____6937) -> begin
false
end
| FStar_Syntax_Syntax.Tm_let (uu____6945) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____6960) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____6980) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____6996) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____7004) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
((maybe_weakly_reduced t1) || (FStar_All.pipe_right args (FStar_Util.for_some (fun uu____7076 -> (match (uu____7076) with
| (a, uu____7087) -> begin
(maybe_weakly_reduced a)
end)))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____7098) -> begin
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
| FStar_Syntax_Syntax.Meta_pattern (uu____7197, args) -> begin
(FStar_Util.for_some (FStar_Util.for_some (fun uu____7252 -> (match (uu____7252) with
| (a, uu____7263) -> begin
(maybe_weakly_reduced a)
end))) args)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____7272, uu____7273, t') -> begin
(maybe_weakly_reduced t')
end
| FStar_Syntax_Syntax.Meta_monadic (uu____7279, t') -> begin
(maybe_weakly_reduced t')
end
| FStar_Syntax_Syntax.Meta_labeled (uu____7285) -> begin
false
end
| FStar_Syntax_Syntax.Meta_desugared (uu____7295) -> begin
false
end
| FStar_Syntax_Syntax.Meta_named (uu____7297) -> begin
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
| uu____7308 -> begin
false
end))


let uu___is_Should_unfold_yes : should_unfold_res  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Should_unfold_yes -> begin
true
end
| uu____7319 -> begin
false
end))


let uu___is_Should_unfold_fully : should_unfold_res  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Should_unfold_fully -> begin
true
end
| uu____7330 -> begin
false
end))


let uu___is_Should_unfold_reify : should_unfold_res  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Should_unfold_reify -> begin
true
end
| uu____7341 -> begin
false
end))


let should_unfold : FStar_TypeChecker_Cfg.cfg  ->  (FStar_TypeChecker_Cfg.cfg  ->  Prims.bool)  ->  FStar_Syntax_Syntax.fv  ->  FStar_TypeChecker_Env.qninfo  ->  should_unfold_res = (fun cfg should_reify1 fv qninfo -> (

let attrs = (

let uu____7374 = (FStar_TypeChecker_Env.attrs_of_qninfo qninfo)
in (match (uu____7374) with
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
| uu____7479 -> begin
no
end))
in (

let fullyno = (fun b -> (match (b) with
| true -> begin
fully
end
| uu____7508 -> begin
no
end))
in (

let comb_or = (fun l -> (FStar_List.fold_right (fun uu____7573 uu____7574 -> (match (((uu____7573), (uu____7574))) with
| ((a, b, c), (x, y, z)) -> begin
(((a || x)), ((b || y)), ((c || z)))
end)) l ((false), (false), (false))))
in (

let string_of_res = (fun uu____7680 -> (match (uu____7680) with
| (x, y, z) -> begin
(

let uu____7700 = (FStar_Util.string_of_bool x)
in (

let uu____7702 = (FStar_Util.string_of_bool y)
in (

let uu____7704 = (FStar_Util.string_of_bool z)
in (FStar_Util.format3 "(%s,%s,%s)" uu____7700 uu____7702 uu____7704))))
end))
in (

let res = if (FStar_TypeChecker_Env.qninfo_is_action qninfo) then begin
(

let b = (should_reify1 cfg)
in ((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7732 -> (

let uu____7733 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____7735 = (FStar_Util.string_of_bool b)
in (FStar_Util.print2 "should_unfold: For DM4F action %s, should_reify = %s\n" uu____7733 uu____7735)))));
(match (b) with
| true -> begin
reif
end
| uu____7748 -> begin
no
end);
))
end else begin
if (

let uu____7750 = (FStar_TypeChecker_Cfg.find_prim_step cfg fv)
in (FStar_Option.isSome uu____7750)) then begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7755 -> (FStar_Util.print_string " >> It\'s a primop, not unfolding\n")));
no;
)
end else begin
(match (((qninfo), (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_only), (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_fully), (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_attr))) with
| (FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, uu____7790), uu____7791); FStar_Syntax_Syntax.sigrng = uu____7792; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____7794; FStar_Syntax_Syntax.sigattrs = uu____7795}, uu____7796), uu____7797), uu____7798, uu____7799, uu____7800) when (FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect qs) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7907 -> (FStar_Util.print_string " >> HasMaskedEffect, not unfolding\n")));
no;
)
end
| (uu____7909, uu____7910, uu____7911, uu____7912) when (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_tac && (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.tac_opaque_attr) attrs)) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____7979 -> (FStar_Util.print_string " >> tac_opaque, not unfolding\n")));
no;
)
end
| (FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, uu____7982), uu____7983); FStar_Syntax_Syntax.sigrng = uu____7984; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____7986; FStar_Syntax_Syntax.sigattrs = uu____7987}, uu____7988), uu____7989), uu____7990, uu____7991, uu____7992) when (is_rec && (not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta))) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8099 -> (FStar_Util.print_string " >> It\'s a recursive definition but we\'re not doing Zeta, not unfolding\n")));
no;
)
end
| (uu____8101, FStar_Pervasives_Native.Some (uu____8102), uu____8103, uu____8104) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8172 -> (

let uu____8173 = (FStar_Syntax_Print.fv_to_string fv)
in (FStar_Util.print1 "should_unfold: Reached a %s with selective unfolding\n" uu____8173))));
(

let uu____8176 = (

let uu____8188 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_only) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8214 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left yesno uu____8214))
end)
in (

let uu____8226 = (

let uu____8238 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_attr) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8264 = (FStar_Util.for_some (fun at -> (FStar_Util.for_some (fun lid -> (FStar_Syntax_Util.is_fvar lid at)) lids)) attrs)
in (FStar_All.pipe_left yesno uu____8264))
end)
in (

let uu____8280 = (

let uu____8292 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_fully) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8318 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left fullyno uu____8318))
end)
in (uu____8292)::[])
in (uu____8238)::uu____8280))
in (uu____8188)::uu____8226))
in (comb_or uu____8176));
)
end
| (uu____8366, uu____8367, FStar_Pervasives_Native.Some (uu____8368), uu____8369) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8437 -> (

let uu____8438 = (FStar_Syntax_Print.fv_to_string fv)
in (FStar_Util.print1 "should_unfold: Reached a %s with selective unfolding\n" uu____8438))));
(

let uu____8441 = (

let uu____8453 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_only) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8479 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left yesno uu____8479))
end)
in (

let uu____8491 = (

let uu____8503 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_attr) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8529 = (FStar_Util.for_some (fun at -> (FStar_Util.for_some (fun lid -> (FStar_Syntax_Util.is_fvar lid at)) lids)) attrs)
in (FStar_All.pipe_left yesno uu____8529))
end)
in (

let uu____8545 = (

let uu____8557 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_fully) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8583 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left fullyno uu____8583))
end)
in (uu____8557)::[])
in (uu____8503)::uu____8545))
in (uu____8453)::uu____8491))
in (comb_or uu____8441));
)
end
| (uu____8631, uu____8632, uu____8633, FStar_Pervasives_Native.Some (uu____8634)) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8702 -> (

let uu____8703 = (FStar_Syntax_Print.fv_to_string fv)
in (FStar_Util.print1 "should_unfold: Reached a %s with selective unfolding\n" uu____8703))));
(

let uu____8706 = (

let uu____8718 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_only) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8744 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left yesno uu____8744))
end)
in (

let uu____8756 = (

let uu____8768 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_attr) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8794 = (FStar_Util.for_some (fun at -> (FStar_Util.for_some (fun lid -> (FStar_Syntax_Util.is_fvar lid at)) lids)) attrs)
in (FStar_All.pipe_left yesno uu____8794))
end)
in (

let uu____8810 = (

let uu____8822 = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_fully) with
| FStar_Pervasives_Native.None -> begin
no
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____8848 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (FStar_All.pipe_left fullyno uu____8848))
end)
in (uu____8822)::[])
in (uu____8768)::uu____8810))
in (uu____8718)::uu____8756))
in (comb_or uu____8706));
)
end
| uu____8896 -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8942 -> (

let uu____8943 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____8945 = (FStar_Syntax_Print.delta_depth_to_string fv.FStar_Syntax_Syntax.fv_delta)
in (

let uu____8947 = (FStar_Common.string_of_list FStar_TypeChecker_Env.string_of_delta_level cfg.FStar_TypeChecker_Cfg.delta_level)
in (FStar_Util.print3 "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n" uu____8943 uu____8945 uu____8947))))));
(

let uu____8950 = (FStar_All.pipe_right cfg.FStar_TypeChecker_Cfg.delta_level (FStar_Util.for_some (fun uu___13_8956 -> (match (uu___13_8956) with
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

let uu____8962 = (FStar_TypeChecker_Env.delta_depth_of_fv cfg.FStar_TypeChecker_Cfg.tcenv fv)
in (FStar_TypeChecker_Common.delta_depth_greater_than uu____8962 l))
end))))
in (FStar_All.pipe_left yesno uu____8950));
)
end)
end
end
in ((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____8978 -> (

let uu____8979 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____8981 = (

let uu____8983 = (FStar_Syntax_Syntax.range_of_fv fv)
in (FStar_Range.string_of_range uu____8983))
in (

let uu____8984 = (string_of_res res)
in (FStar_Util.print3 "should_unfold: For %s (%s), unfolding res = %s\n" uu____8979 uu____8981 uu____8984))))));
(match (res) with
| (false, uu____8987, uu____8988) -> begin
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
| uu____9013 -> begin
(

let uu____9023 = (

let uu____9025 = (string_of_res res)
in (FStar_Util.format1 "Unexpected unfolding result: %s" uu____9025))
in (FStar_All.pipe_left failwith uu____9023))
end);
))))))))))))


let decide_unfolding : 'Auu____9044 . FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack_elt Prims.list  ->  'Auu____9044  ->  FStar_Syntax_Syntax.fv  ->  FStar_TypeChecker_Env.qninfo  ->  (FStar_TypeChecker_Cfg.cfg * stack_elt Prims.list) FStar_Pervasives_Native.option = (fun cfg env stack rng fv qninfo -> (

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

let uu___1159_9113 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___1161_9116 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___1161_9116.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___1161_9116.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___1161_9116.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___1161_9116.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___1161_9116.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___1161_9116.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___1161_9116.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant); FStar_TypeChecker_Cfg.unfold_only = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_fully = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_attr = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_tac = uu___1161_9116.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___1161_9116.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___1161_9116.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___1161_9116.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___1161_9116.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___1161_9116.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___1161_9116.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___1161_9116.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___1161_9116.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___1161_9116.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___1161_9116.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___1161_9116.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___1161_9116.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___1161_9116.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___1161_9116.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___1159_9113.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1159_9113.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1159_9113.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1159_9113.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1159_9113.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1159_9113.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1159_9113.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1159_9113.FStar_TypeChecker_Cfg.reifying})
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

let uu____9178 = (push1 e t)
in (UnivArgs (((us), (r))))::uu____9178)
end
| (h)::t -> begin
(e)::(h)::t
end))
in (

let ref = (

let uu____9190 = (

let uu____9197 = (

let uu____9198 = (

let uu____9199 = (FStar_Syntax_Syntax.lid_of_fv fv)
in FStar_Const.Const_reflect (uu____9199))
in FStar_Syntax_Syntax.Tm_constant (uu____9198))
in (FStar_Syntax_Syntax.mk uu____9197))
in (uu____9190 FStar_Pervasives_Native.None FStar_Range.dummyRange))
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

let uu____9265 = (

let uu____9266 = (FStar_Syntax_Subst.compress t)
in uu____9266.FStar_Syntax_Syntax.n)
in (match (uu____9265) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____9297 = (

let uu____9298 = (FStar_Syntax_Util.un_uinst hd1)
in uu____9298.FStar_Syntax_Syntax.n)
in (match (uu____9297) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((is_on_dom fv) && (Prims.op_Equality (FStar_List.length args) (Prims.parse_int "3"))) -> begin
(

let f = (

let uu____9315 = (

let uu____9322 = (

let uu____9333 = (FStar_All.pipe_right args FStar_List.tl)
in (FStar_All.pipe_right uu____9333 FStar_List.tl))
in (FStar_All.pipe_right uu____9322 FStar_List.hd))
in (FStar_All.pipe_right uu____9315 FStar_Pervasives_Native.fst))
in FStar_Pervasives_Native.Some (f))
end
| uu____9432 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____9433 -> begin
FStar_Pervasives_Native.None
end))))))


let rec norm : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t1 = ((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.norm_delayed) with
| true -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____9712) -> begin
(

let uu____9735 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "NORM delayed: %s\n" uu____9735))
end
| uu____9738 -> begin
()
end)
end
| uu____9739 -> begin
()
end);
(FStar_Syntax_Subst.compress t);
)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____9748 -> (

let uu____9749 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____9751 = (FStar_Util.string_of_bool cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.no_full_norm)
in (

let uu____9753 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____9755 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____9763 = (

let uu____9765 = (

let uu____9768 = (firstn (Prims.parse_int "4") stack)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9768))
in (stack_to_string uu____9765))
in (FStar_Util.print5 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n" uu____9749 uu____9751 uu____9753 uu____9755 uu____9763))))))));
(FStar_TypeChecker_Cfg.log_cfg cfg (fun uu____9796 -> (

let uu____9797 = (FStar_TypeChecker_Cfg.cfg_to_string cfg)
in (FStar_Util.print1 ">>> cfg = %s\n" uu____9797))));
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9803 -> (

let uu____9804 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9804))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_constant (uu____9807) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9811 -> (

let uu____9812 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9812))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_name (uu____9815) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9819 -> (

let uu____9820 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9820))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_lazy (uu____9823) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9827 -> (

let uu____9828 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9828))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____9831; FStar_Syntax_Syntax.fv_delta = uu____9832; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9836 -> (

let uu____9837 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9837))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____9840; FStar_Syntax_Syntax.fv_delta = uu____9841; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____9842))}) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9852 -> (

let uu____9853 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9853))));
(rebuild cfg env stack t1);
)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let qninfo = (FStar_TypeChecker_Env.lookup_qname cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (

let uu____9859 = (FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo)
in (match (uu____9859) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level (_9862)) when (_9862 = (Prims.parse_int "0")) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____9866 -> (

let uu____9867 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu____9867))));
(rebuild cfg env stack t1);
)
end
| uu____9870 -> begin
(

let uu____9873 = (decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv qninfo)
in (match (uu____9873) with
| FStar_Pervasives_Native.Some (cfg1, stack1) -> begin
(do_unfold_fv cfg1 env stack1 t1 qninfo fv)
end
| FStar_Pervasives_Native.None -> begin
(rebuild cfg env stack t1)
end))
end))))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____9900) -> begin
(

let uu____9907 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____9907))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when ((should_consider_norm_requests cfg) && (

let uu____9935 = (is_norm_request hd1 args)
in (Prims.op_Equality uu____9935 Norm_request_requires_rejig))) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(FStar_Util.print_string "Rejigging norm request ... \n")
end
| uu____9939 -> begin
()
end);
(

let uu____9941 = (rejig_norm_request hd1 args)
in (norm cfg env stack uu____9941));
)
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when ((should_consider_norm_requests cfg) && (

let uu____9969 = (is_norm_request hd1 args)
in (Prims.op_Equality uu____9969 Norm_request_ready))) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(FStar_Util.print_string "Potential norm request ... \n")
end
| uu____9973 -> begin
()
end);
(

let cfg' = (

let uu___1269_9976 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___1271_9979 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___1271_9979.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___1271_9979.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___1271_9979.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___1271_9979.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___1271_9979.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___1271_9979.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = false; FStar_TypeChecker_Cfg.unfold_until = uu___1271_9979.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_fully = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_attr = uu___1271_9979.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___1271_9979.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___1271_9979.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___1271_9979.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___1271_9979.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___1271_9979.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___1271_9979.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___1271_9979.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___1271_9979.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___1271_9979.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___1271_9979.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___1271_9979.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___1271_9979.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___1271_9979.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___1271_9979.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___1271_9979.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___1269_9976.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1269_9976.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]; FStar_TypeChecker_Cfg.primitive_steps = uu___1269_9976.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1269_9976.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1269_9976.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = true; FStar_TypeChecker_Cfg.reifying = uu___1269_9976.FStar_TypeChecker_Cfg.reifying})
in (

let uu____9986 = (get_norm_request cfg (norm cfg' env []) args)
in (match (uu____9986) with
| FStar_Pervasives_Native.None -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(FStar_Util.print_string "Norm request None ... \n")
end
| uu____10006 -> begin
()
end);
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____10022 stack1 -> (match (uu____10022) with
| (a, aq) -> begin
(

let uu____10034 = (

let uu____10035 = (

let uu____10042 = (

let uu____10043 = (

let uu____10075 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____10075), (false)))
in Clos (uu____10043))
in ((uu____10042), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____10035))
in (uu____10034)::stack1)
end)) args))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10143 -> (

let uu____10144 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____10144))));
(norm cfg env stack1 hd1);
));
)
end
| FStar_Pervasives_Native.Some (s, tm) when (is_nbe_request s) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(

let uu____10171 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Starting NBE request on %s ... \n" uu____10171))
end
| uu____10174 -> begin
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

let uu____10182 = (

let uu____10184 = (

let uu____10186 = (FStar_Util.time_diff start fin)
in (FStar_Pervasives_Native.snd uu____10186))
in (FStar_Util.string_of_int uu____10184))
in (

let uu____10193 = (FStar_Syntax_Print.term_to_string tm')
in (

let uu____10195 = (FStar_Syntax_Print.term_to_string tm_norm)
in (FStar_Util.print3 "NBE\'d (%s ms) %s\n\tto %s\n" uu____10182 uu____10193 uu____10195))))
end
| uu____10198 -> begin
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

let uu____10214 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Starting norm request on %s ... \n" uu____10214))
end
| uu____10217 -> begin
()
end);
(

let delta_level = (

let uu____10222 = (FStar_All.pipe_right s (FStar_Util.for_some (fun uu___14_10229 -> (match (uu___14_10229) with
| FStar_TypeChecker_Env.UnfoldUntil (uu____10231) -> begin
true
end
| FStar_TypeChecker_Env.UnfoldOnly (uu____10233) -> begin
true
end
| FStar_TypeChecker_Env.UnfoldFully (uu____10237) -> begin
true
end
| uu____10241 -> begin
false
end))))
in (match (uu____10222) with
| true -> begin
(FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]
end
| uu____10246 -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end))
in (

let cfg'1 = (

let uu___1312_10249 = cfg
in (

let uu____10250 = (

let uu___1314_10251 = (FStar_TypeChecker_Cfg.to_fsteps s)
in {FStar_TypeChecker_Cfg.beta = uu___1314_10251.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___1314_10251.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___1314_10251.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___1314_10251.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___1314_10251.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___1314_10251.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___1314_10251.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___1314_10251.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___1314_10251.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___1314_10251.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___1314_10251.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___1314_10251.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___1314_10251.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___1314_10251.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___1314_10251.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___1314_10251.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___1314_10251.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___1314_10251.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___1314_10251.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___1314_10251.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___1314_10251.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___1314_10251.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = true; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___1314_10251.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___1314_10251.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___1314_10251.FStar_TypeChecker_Cfg.for_extraction})
in {FStar_TypeChecker_Cfg.steps = uu____10250; FStar_TypeChecker_Cfg.tcenv = uu___1312_10249.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1312_10249.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1312_10249.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1312_10249.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1312_10249.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = true; FStar_TypeChecker_Cfg.reifying = uu___1312_10249.FStar_TypeChecker_Cfg.reifying}))
in (

let stack' = (

let tail1 = (Cfg (cfg))::stack
in (match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.print_normalized) with
| true -> begin
(

let uu____10259 = (

let uu____10260 = (

let uu____10265 = (FStar_Util.now ())
in ((t1), (uu____10265)))
in Debug (uu____10260))
in (uu____10259)::tail1)
end
| uu____10266 -> begin
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

let uu____10270 = (mk (FStar_Syntax_Syntax.Tm_type (u1)) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack uu____10270)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.erase_universes) with
| true -> begin
(norm cfg env stack t')
end
| uu____10278 -> begin
(

let us1 = (

let uu____10281 = (

let uu____10288 = (FStar_List.map (norm_universe cfg env) us)
in ((uu____10288), (t1.FStar_Syntax_Syntax.pos)))
in UnivArgs (uu____10281))
in (

let stack1 = (us1)::stack
in (norm cfg env stack1 t')))
end)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____10297 = (lookup_bvar env x)
in (match (uu____10297) with
| Univ (uu____10298) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env1, t0, r, fix) -> begin
(match (((not (fix)) || cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta)) with
| true -> begin
(

let uu____10352 = (FStar_ST.op_Bang r)
in (match (uu____10352) with
| FStar_Pervasives_Native.Some (env2, t') -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____10448 -> (

let uu____10449 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10451 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" uu____10449 uu____10451)))));
(

let uu____10454 = (maybe_weakly_reduced t')
in (match (uu____10454) with
| true -> begin
(match (stack) with
| [] when (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak || cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars) -> begin
(rebuild cfg env2 stack t')
end
| uu____10457 -> begin
(norm cfg env2 stack t')
end)
end
| uu____10458 -> begin
(rebuild cfg env2 stack t')
end));
)
end
| FStar_Pervasives_Native.None -> begin
(norm cfg env1 ((MemoLazy (r))::stack) t0)
end))
end
| uu____10472 -> begin
(norm cfg env1 stack t0)
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack) with
| (UnivArgs (uu____10501))::uu____10502 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Arg (c, uu____10513, uu____10514))::stack_rest -> begin
(match (c) with
| Univ (uu____10518) -> begin
(norm cfg ((((FStar_Pervasives_Native.None), (c)))::env) stack_rest t1)
end
| uu____10527 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (b)::[] -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____10557 -> (

let uu____10558 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____10558))));
(norm cfg ((((FStar_Pervasives_Native.Some (b)), (c)))::env) stack_rest body);
)
end
| (b)::tl1 -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____10594 -> (

let uu____10595 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____10595))));
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
(FStar_TypeChecker_Cfg.log cfg (fun uu____10643 -> (

let uu____10644 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____10644))));
(norm cfg env stack1 t1);
)
end
| (Match (uu____10647))::uu____10648 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____10661 -> begin
(

let uu____10663 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____10663) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____10699 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____10743 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____10743))))
end
| uu____10744 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1432_10751 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1432_10751.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1432_10751.FStar_Syntax_Syntax.residual_flags})))
end
| uu____10752 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10758 -> (

let uu____10759 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____10759))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1439_10774 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1439_10774.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1439_10774.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1439_10774.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1439_10774.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1439_10774.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1439_10774.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1439_10774.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1439_10774.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Debug (uu____10778))::uu____10779 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____10788 -> begin
(

let uu____10790 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____10790) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____10826 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____10870 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____10870))))
end
| uu____10871 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1432_10878 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1432_10878.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1432_10878.FStar_Syntax_Syntax.residual_flags})))
end
| uu____10879 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____10885 -> (

let uu____10886 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____10886))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1439_10901 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1439_10901.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1439_10901.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1439_10901.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1439_10901.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1439_10901.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1439_10901.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1439_10901.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1439_10901.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Meta (uu____10905))::uu____10906 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____10917 -> begin
(

let uu____10919 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____10919) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____10955 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____10999 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____10999))))
end
| uu____11000 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1432_11007 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1432_11007.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1432_11007.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11008 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11014 -> (

let uu____11015 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11015))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1439_11030 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1439_11030.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1439_11030.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1439_11030.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1439_11030.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1439_11030.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1439_11030.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1439_11030.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1439_11030.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Let (uu____11034))::uu____11035 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____11048 -> begin
(

let uu____11050 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11050) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11086 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11130 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11130))))
end
| uu____11131 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1432_11138 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1432_11138.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1432_11138.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11139 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11145 -> (

let uu____11146 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11146))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1439_11161 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1439_11161.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1439_11161.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1439_11161.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1439_11161.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1439_11161.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1439_11161.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1439_11161.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1439_11161.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (App (uu____11165))::uu____11166 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____11179 -> begin
(

let uu____11181 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11181) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11217 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11261 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11261))))
end
| uu____11262 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1432_11269 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1432_11269.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1432_11269.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11270 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11276 -> (

let uu____11277 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11277))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1439_11292 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1439_11292.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1439_11292.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1439_11292.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1439_11292.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1439_11292.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1439_11292.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1439_11292.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1439_11292.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Abs (uu____11296))::uu____11297 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let t2 = (closure_as_term cfg env t1)
in (rebuild cfg env stack t2))
end
| uu____11314 -> begin
(

let uu____11316 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11316) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11352 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11396 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11396))))
end
| uu____11397 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1432_11404 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1432_11404.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1432_11404.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11405 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11411 -> (

let uu____11412 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11412))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1439_11427 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1439_11427.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1439_11427.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1439_11427.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1439_11427.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1439_11427.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1439_11427.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1439_11427.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1439_11427.FStar_TypeChecker_Cfg.reifying})
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
| uu____11433 -> begin
(

let uu____11435 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____11435) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11471 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____11515 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____11515))))
end
| uu____11516 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___1432_11523 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___1432_11523.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___1432_11523.FStar_Syntax_Syntax.residual_flags})))
end
| uu____11524 -> begin
lopt
end)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11530 -> (

let uu____11531 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____11531))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1439_11546 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1439_11546.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1439_11546.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1439_11546.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1439_11546.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1439_11546.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1439_11546.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1439_11546.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1439_11546.FStar_TypeChecker_Cfg.reifying})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____11590 stack1 -> (match (uu____11590) with
| (a, aq) -> begin
(

let uu____11602 = (

let uu____11603 = (

let uu____11610 = (

let uu____11611 = (

let uu____11643 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____11643), (false)))
in Clos (uu____11611))
in ((uu____11610), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____11603))
in (uu____11602)::stack1)
end)) args))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____11711 -> (

let uu____11712 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____11712))));
(norm cfg env stack1 head1);
))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____11726) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.for_extraction -> begin
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

let uu___1466_11771 = x
in {FStar_Syntax_Syntax.ppname = uu___1466_11771.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1466_11771.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t2)))
end
| uu____11772 -> begin
(

let uu____11787 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____11787))
end)
end
| uu____11788 -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let uu____11791 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____11791) with
| (closing, f1) -> begin
(

let f2 = (norm cfg ((dummy)::env) [] f1)
in (

let t2 = (

let uu____11822 = (

let uu____11823 = (

let uu____11830 = (FStar_Syntax_Subst.close closing f2)
in (((

let uu___1475_11836 = x
in {FStar_Syntax_Syntax.ppname = uu___1475_11836.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1475_11836.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (uu____11830)))
in FStar_Syntax_Syntax.Tm_refine (uu____11823))
in (mk uu____11822 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t2)))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
(

let uu____11860 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____11860))
end
| uu____11861 -> begin
(

let uu____11863 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____11863) with
| (bs1, c1) -> begin
(

let c2 = (

let uu____11871 = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____11897 -> (dummy)::env1) env))
in (norm_comp cfg uu____11871 c1))
in (

let t2 = (

let uu____11921 = (norm_binders cfg env bs1)
in (FStar_Syntax_Util.arrow uu____11921 c2))
in (rebuild cfg env stack t2)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unascribe -> begin
(norm cfg env stack t11)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) -> begin
(match (stack) with
| (Match (uu____12034))::uu____12035 when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.beta -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12048 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (Arg (uu____12050))::uu____12051 when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.beta -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12062 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (App (uu____12064, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____12065; FStar_Syntax_Syntax.vars = uu____12066}, uu____12067, uu____12068))::uu____12069 when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.beta -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12076 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (MemoLazy (uu____12078))::uu____12079 when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.beta -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12090 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| uu____12092 -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12095 -> (FStar_Util.print_string "+++ Keeping ascription \n")));
(

let t12 = (norm cfg env [] t11)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____12100 -> (FStar_Util.print_string "+++ Normalizing ascription \n")));
(

let tc1 = (match (tc) with
| FStar_Util.Inl (t2) -> begin
(

let uu____12126 = (norm cfg env [] t2)
in FStar_Util.Inl (uu____12126))
end
| FStar_Util.Inr (c) -> begin
(

let uu____12140 = (norm_comp cfg env c)
in FStar_Util.Inr (uu____12140))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (norm cfg env []))
in (match (stack) with
| (Cfg (cfg1))::stack1 -> begin
(

let t2 = (

let uu____12163 = (

let uu____12164 = (

let uu____12191 = (FStar_Syntax_Util.unascribe t12)
in ((uu____12191), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____12164))
in (mk uu____12163 t1.FStar_Syntax_Syntax.pos))
in (norm cfg1 env stack1 t2))
end
| uu____12226 -> begin
(

let uu____12227 = (

let uu____12228 = (

let uu____12229 = (

let uu____12256 = (FStar_Syntax_Util.unascribe t12)
in ((uu____12256), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____12229))
in (mk uu____12228 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack uu____12227))
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

let uu___1554_12334 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___1556_12337 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___1556_12337.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___1556_12337.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___1556_12337.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = true; FStar_TypeChecker_Cfg.hnf = uu___1556_12337.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___1556_12337.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___1556_12337.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___1556_12337.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___1556_12337.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___1556_12337.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___1556_12337.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___1556_12337.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___1556_12337.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___1556_12337.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___1556_12337.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___1556_12337.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___1556_12337.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___1556_12337.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___1556_12337.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___1556_12337.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___1556_12337.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___1556_12337.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___1556_12337.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___1556_12337.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___1556_12337.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___1556_12337.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___1554_12334.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1554_12334.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1554_12334.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1554_12334.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1554_12334.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1554_12334.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1554_12334.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1554_12334.FStar_TypeChecker_Cfg.reifying})
in (norm cfg' env ((Cfg (cfg))::stack1) head1))
end
| uu____12339 -> begin
(norm cfg env stack1 head1)
end))
end
| FStar_Syntax_Syntax.Tm_let ((b, lbs), lbody) when ((FStar_Syntax_Syntax.is_top_level lbs) && cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____12378 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____12378) with
| (openings, lbunivs) -> begin
(

let cfg1 = (

let uu___1569_12398 = cfg
in (

let uu____12399 = (FStar_TypeChecker_Env.push_univ_vars cfg.FStar_TypeChecker_Cfg.tcenv lbunivs)
in {FStar_TypeChecker_Cfg.steps = uu___1569_12398.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu____12399; FStar_TypeChecker_Cfg.debug = uu___1569_12398.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1569_12398.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1569_12398.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1569_12398.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1569_12398.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1569_12398.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1569_12398.FStar_TypeChecker_Cfg.reifying}))
in (

let norm1 = (fun t2 -> (

let uu____12406 = (

let uu____12407 = (FStar_Syntax_Subst.subst openings t2)
in (norm cfg1 env [] uu____12407))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____12406)))
in (

let lbtyp = (norm1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (norm1 lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___1576_12410 = lb
in {FStar_Syntax_Syntax.lbname = uu___1576_12410.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___1576_12410.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___1576_12410.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1576_12410.FStar_Syntax_Syntax.lbpos})))))
end)))))
in (

let uu____12411 = (mk (FStar_Syntax_Syntax.Tm_let (((((b), (lbs1))), (lbody)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack uu____12411)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____12424, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____12425); FStar_Syntax_Syntax.lbunivs = uu____12426; FStar_Syntax_Syntax.lbtyp = uu____12427; FStar_Syntax_Syntax.lbeff = uu____12428; FStar_Syntax_Syntax.lbdef = uu____12429; FStar_Syntax_Syntax.lbattrs = uu____12430; FStar_Syntax_Syntax.lbpos = uu____12431})::uu____12432), uu____12433) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n1 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in (

let uu____12479 = ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets)) && (((cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.pure_subterms_within_computations && (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs FStar_Parser_Const.inline_let_attr)) || ((FStar_Syntax_Util.is_pure_effect n1) && (cfg.FStar_TypeChecker_Cfg.normalize_pure_lets || (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs FStar_Parser_Const.inline_let_attr)))) || ((FStar_Syntax_Util.is_ghost_effect n1) && (not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.pure_subterms_within_computations)))))
in (match (uu____12479) with
| true -> begin
(

let binder = (

let uu____12483 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____12483))
in (

let env1 = (

let uu____12493 = (

let uu____12500 = (

let uu____12501 = (

let uu____12533 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (uu____12533), (false)))
in Clos (uu____12501))
in ((FStar_Pervasives_Native.Some (binder)), (uu____12500)))
in (uu____12493)::env)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____12608 -> (FStar_Util.print_string "+++ Reducing Tm_let\n")));
(norm cfg env1 stack body);
)))
end
| uu____12610 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak) with
| true -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12615 -> (FStar_Util.print_string "+++ Not touching Tm_let\n")));
(

let uu____12617 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____12617));
)
end
| uu____12618 -> begin
(

let uu____12620 = (

let uu____12625 = (

let uu____12626 = (

let uu____12633 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right uu____12633 FStar_Syntax_Syntax.mk_binder))
in (uu____12626)::[])
in (FStar_Syntax_Subst.open_term uu____12625 body))
in (match (uu____12620) with
| (bs, body1) -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____12660 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- type")));
(

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let x = (

let uu____12669 = (FStar_List.hd bs)
in (FStar_Pervasives_Native.fst uu____12669))
in FStar_Util.Inl ((

let uu___1618_12685 = x
in {FStar_Syntax_Syntax.ppname = uu___1618_12685.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1618_12685.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____12688 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- definiens\n")));
(

let lb1 = (

let uu___1623_12691 = lb
in (

let uu____12692 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___1623_12691.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___1623_12691.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____12692; FStar_Syntax_Syntax.lbattrs = uu___1623_12691.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1623_12691.FStar_Syntax_Syntax.lbpos}))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env1 uu____12721 -> (dummy)::env1) env))
in (

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___1630_12746 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1630_12746.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1630_12746.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1630_12746.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1630_12746.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1630_12746.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___1630_12746.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1630_12746.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1630_12746.FStar_TypeChecker_Cfg.reifying})
in ((FStar_TypeChecker_Cfg.log cfg1 (fun uu____12750 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- body\n")));
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

let uu____12771 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____12771) with
| (lbs1, body1) -> begin
(

let lbs2 = (FStar_List.map (fun lb -> (

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let uu____12807 = (

let uu___1646_12808 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___1646_12808.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1646_12808.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})
in FStar_Util.Inl (uu____12807))
in (

let uu____12809 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____12809) with
| (xs, def_body, lopt) -> begin
(

let xs1 = (norm_binders cfg env xs)
in (

let env1 = (

let uu____12835 = (FStar_List.map (fun uu____12851 -> dummy) lbs1)
in (

let uu____12852 = (

let uu____12861 = (FStar_List.map (fun uu____12883 -> dummy) xs1)
in (FStar_List.append uu____12861 env))
in (FStar_List.append uu____12835 uu____12852)))
in (

let def_body1 = (norm cfg env1 [] def_body)
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____12909 = (

let uu___1660_12910 = rc
in (

let uu____12911 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env1 []))
in {FStar_Syntax_Syntax.residual_effect = uu___1660_12910.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____12911; FStar_Syntax_Syntax.residual_flags = uu___1660_12910.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____12909))
end
| uu____12920 -> begin
lopt
end)
in (

let def = (FStar_Syntax_Util.abs xs1 def_body1 lopt1)
in (

let uu___1665_12926 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___1665_12926.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___1665_12926.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___1665_12926.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1665_12926.FStar_Syntax_Syntax.lbpos}))))))
end))))) lbs1)
in (

let env' = (

let uu____12936 = (FStar_List.map (fun uu____12952 -> dummy) lbs2)
in (FStar_List.append uu____12936 env))
in (

let body2 = (norm cfg env' [] body1)
in (

let uu____12960 = (FStar_Syntax_Subst.close_let_rec lbs2 body2)
in (match (uu____12960) with
| (lbs3, body3) -> begin
(

let t2 = (

let uu___1674_12976 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (body3))); FStar_Syntax_Syntax.pos = uu___1674_12976.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___1674_12976.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack t2))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta)) -> begin
(

let uu____13010 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____13010))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let uu____13031 = (FStar_List.fold_right (fun lb uu____13109 -> (match (uu____13109) with
| (rec_env, memos, i) -> begin
(

let bv = (

let uu___1690_13234 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___1690_13234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___1690_13234.FStar_Syntax_Syntax.sort})
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
in (match (uu____13031) with
| (rec_env, memos, uu____13425) -> begin
(

let uu____13480 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (FStar_Pervasives_Native.Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (FStar_Pervasives_Native.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env1 -> (

let uu____13729 = (

let uu____13736 = (

let uu____13737 = (

let uu____13769 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (uu____13769), (false)))
in Clos (uu____13737))
in ((FStar_Pervasives_Native.None), (uu____13736)))
in (uu____13729)::env1)) (FStar_Pervasives_Native.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head1, m) -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____13854 -> (

let uu____13855 = (FStar_Syntax_Print.metadata_to_string m)
in (FStar_Util.print1 ">> metadata = %s\n" uu____13855))));
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m1, t2) -> begin
(reduce_impure_comp cfg env stack head1 (FStar_Util.Inl (m1)) t2)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) -> begin
(reduce_impure_comp cfg env stack head1 (FStar_Util.Inr (((m1), (m')))) t2)
end
| uu____13879 -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unmeta) with
| true -> begin
(norm cfg env stack head1)
end
| uu____13881 -> begin
(match (stack) with
| (uu____13883)::uu____13884 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____13889) -> begin
(norm cfg env ((Meta (((env), (m), (r))))::stack) head1)
end
| FStar_Syntax_Syntax.Meta_pattern (names1, args) -> begin
(

let args1 = (norm_pattern_args cfg env args)
in (

let names2 = (FStar_All.pipe_right names1 (FStar_List.map (norm cfg env [])))
in (norm cfg env ((Meta (((env), (FStar_Syntax_Syntax.Meta_pattern (((names2), (args1)))), (t1.FStar_Syntax_Syntax.pos))))::stack) head1)))
end
| uu____13968 -> begin
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

let uu____14016 = (

let uu____14037 = (norm_pattern_args cfg env args)
in ((names2), (uu____14037)))
in FStar_Syntax_Syntax.Meta_pattern (uu____14016)))
end
| uu____14066 -> begin
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
| FStar_Syntax_Syntax.Tm_delayed (uu____14072) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (norm cfg env stack t2))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____14096) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____14110) -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.check_no_uvars) with
| true -> begin
(

let uu____14124 = (

let uu____14126 = (FStar_Range.string_of_range t2.FStar_Syntax_Syntax.pos)
in (

let uu____14128 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "(%s) CheckNoUvars: Unexpected unification variable remains: %s" uu____14126 uu____14128)))
in (failwith uu____14124))
end
| uu____14131 -> begin
(

let uu____14133 = (inline_closure_env cfg env [] t2)
in (rebuild cfg env stack uu____14133))
end)
end
| uu____14134 -> begin
(norm cfg env stack t2)
end))
end);
)))
and do_unfold_fv : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.qninfo  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t0 qninfo f -> (

let uu____14143 = (FStar_TypeChecker_Env.lookup_definition_qninfo cfg.FStar_TypeChecker_Cfg.delta_level f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v qninfo)
in (match (uu____14143) with
| FStar_Pervasives_Native.None -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____14157 -> (

let uu____14158 = (FStar_Syntax_Print.fv_to_string f)
in (FStar_Util.print1 " >> Tm_fvar case 2 for %s\n" uu____14158))));
(rebuild cfg env stack t0);
)
end
| FStar_Pervasives_Native.Some (us, t) -> begin
((FStar_TypeChecker_Cfg.log_unfolding cfg (fun uu____14171 -> (

let uu____14172 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____14174 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 " >> Unfolded %s to %s\n" uu____14172 uu____14174)))));
(

let t1 = (match ((Prims.op_Equality cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.unfold_until (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)))) with
| true -> begin
t
end
| uu____14181 -> begin
(FStar_Syntax_Subst.set_use_range t0.FStar_Syntax_Syntax.pos t)
end)
in (

let n1 = (FStar_List.length us)
in (match ((n1 > (Prims.parse_int "0"))) with
| true -> begin
(match (stack) with
| (UnivArgs (us', uu____14187))::stack1 -> begin
((

let uu____14196 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv) (FStar_Options.Other ("univ_norm")))
in (match (uu____14196) with
| true -> begin
(FStar_List.iter (fun x -> (

let uu____14204 = (FStar_Syntax_Print.univ_to_string x)
in (FStar_Util.print1 "Univ (normalizer) %s\n" uu____14204))) us')
end
| uu____14207 -> begin
()
end));
(

let env1 = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env1 u -> (((FStar_Pervasives_Native.None), (Univ (u))))::env1) env))
in (norm cfg env1 stack1 t1));
)
end
| uu____14240 when (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.erase_universes || cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.allow_unbound_universes) -> begin
(norm cfg env stack t1)
end
| uu____14243 -> begin
(

let uu____14246 = (

let uu____14248 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" uu____14248))
in (failwith uu____14246))
end)
end
| uu____14251 -> begin
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

let uu___1802_14276 = cfg
in (

let uu____14277 = (FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one new_steps cfg.FStar_TypeChecker_Cfg.steps)
in {FStar_TypeChecker_Cfg.steps = uu____14277; FStar_TypeChecker_Cfg.tcenv = uu___1802_14276.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1802_14276.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = (FStar_TypeChecker_Env.InliningDelta)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; FStar_TypeChecker_Cfg.primitive_steps = uu___1802_14276.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1802_14276.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1802_14276.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1802_14276.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1802_14276.FStar_TypeChecker_Cfg.reifying})))
end
| uu____14278 -> begin
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
| (App (uu____14308, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____14309; FStar_Syntax_Syntax.vars = uu____14310}, uu____14311, uu____14312))::uu____14313 -> begin
()
end
| uu____14318 -> begin
(

let uu____14321 = (

let uu____14323 = (stack_to_string stack)
in (FStar_Util.format1 "INTERNAL ERROR: do_reify_monadic: bad stack: %s" uu____14323))
in (failwith uu____14321))
end);
(

let head0 = head1
in (

let head2 = (FStar_Syntax_Util.unascribe head1)
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____14332 -> (

let uu____14333 = (FStar_Syntax_Print.tag_of_term head2)
in (

let uu____14335 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print2 "Reifying: (%s) %s\n" uu____14333 uu____14335)))));
(

let head3 = (FStar_Syntax_Util.unmeta_safe head2)
in (

let uu____14339 = (

let uu____14340 = (FStar_Syntax_Subst.compress head3)
in uu____14340.FStar_Syntax_Syntax.n)
in (match (uu____14339) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (

let uu____14361 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv m)
in (FStar_TypeChecker_Env.get_effect_decl cfg.FStar_TypeChecker_Cfg.tcenv uu____14361))
in (

let uu____14362 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____14362) with
| (uu____14363, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____14373) -> begin
(failwith "Cannot reify a top-level let binding")
end
| FStar_Util.Inl (x) -> begin
(

let is_return = (fun e -> (

let uu____14384 = (

let uu____14385 = (FStar_Syntax_Subst.compress e)
in uu____14385.FStar_Syntax_Syntax.n)
in (match (uu____14384) with
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____14391, uu____14392)) -> begin
(

let uu____14401 = (

let uu____14402 = (FStar_Syntax_Subst.compress e1)
in uu____14402.FStar_Syntax_Syntax.n)
in (match (uu____14401) with
| FStar_Syntax_Syntax.Tm_meta (e2, FStar_Syntax_Syntax.Meta_monadic_lift (uu____14408, msrc, uu____14410)) when (FStar_Syntax_Util.is_pure_effect msrc) -> begin
(

let uu____14419 = (FStar_Syntax_Subst.compress e2)
in FStar_Pervasives_Native.Some (uu____14419))
end
| uu____14420 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____14421 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____14422 = (is_return lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____14422) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let lb1 = (

let uu___1874_14427 = lb
in {FStar_Syntax_Syntax.lbname = uu___1874_14427.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___1874_14427.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___1874_14427.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu___1874_14427.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1874_14427.FStar_Syntax_Syntax.lbpos})
in (

let uu____14428 = (FStar_List.tl stack)
in (

let uu____14429 = (

let uu____14430 = (

let uu____14437 = (

let uu____14438 = (

let uu____14452 = (FStar_Syntax_Util.mk_reify body)
in ((((false), ((lb1)::[]))), (uu____14452)))
in FStar_Syntax_Syntax.Tm_let (uu____14438))
in (FStar_Syntax_Syntax.mk uu____14437))
in (uu____14430 FStar_Pervasives_Native.None head3.FStar_Syntax_Syntax.pos))
in (norm cfg env uu____14428 uu____14429))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____14468 = (

let uu____14470 = (is_return body)
in (match (uu____14470) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_bvar (y); FStar_Syntax_Syntax.pos = uu____14475; FStar_Syntax_Syntax.vars = uu____14476}) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____14479 -> begin
false
end))
in (match (uu____14468) with
| true -> begin
(norm cfg env stack lb.FStar_Syntax_Syntax.lbdef)
end
| uu____14484 -> begin
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

let uu____14503 = (

let uu____14510 = (

let uu____14511 = (

let uu____14530 = (

let uu____14539 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____14539)::[])
in ((uu____14530), (body1), (FStar_Pervasives_Native.Some (body_rc))))
in FStar_Syntax_Syntax.Tm_abs (uu____14511))
in (FStar_Syntax_Syntax.mk uu____14510))
in (uu____14503 FStar_Pervasives_Native.None body1.FStar_Syntax_Syntax.pos))
in (

let close1 = (closure_as_term cfg env)
in (

let bind_inst = (

let uu____14578 = (

let uu____14579 = (FStar_Syntax_Subst.compress bind_repr)
in uu____14579.FStar_Syntax_Syntax.n)
in (match (uu____14578) with
| FStar_Syntax_Syntax.Tm_uinst (bind1, (uu____14585)::(uu____14586)::[]) -> begin
(

let uu____14591 = (

let uu____14598 = (

let uu____14599 = (

let uu____14606 = (

let uu____14607 = (

let uu____14608 = (close1 lb.FStar_Syntax_Syntax.lbtyp)
in (cfg.FStar_TypeChecker_Cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.FStar_TypeChecker_Cfg.tcenv uu____14608))
in (

let uu____14609 = (

let uu____14612 = (

let uu____14613 = (close1 t)
in (cfg.FStar_TypeChecker_Cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.FStar_TypeChecker_Cfg.tcenv uu____14613))
in (uu____14612)::[])
in (uu____14607)::uu____14609))
in ((bind1), (uu____14606)))
in FStar_Syntax_Syntax.Tm_uinst (uu____14599))
in (FStar_Syntax_Syntax.mk uu____14598))
in (uu____14591 FStar_Pervasives_Native.None rng))
end
| uu____14616 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let maybe_range_arg = (

let uu____14631 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____14631) with
| true -> begin
(

let uu____14644 = (

let uu____14653 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range lb.FStar_Syntax_Syntax.lbpos lb.FStar_Syntax_Syntax.lbpos)
in (FStar_Syntax_Syntax.as_arg uu____14653))
in (

let uu____14654 = (

let uu____14665 = (

let uu____14674 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range body2.FStar_Syntax_Syntax.pos body2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.as_arg uu____14674))
in (uu____14665)::[])
in (uu____14644)::uu____14654))
end
| uu____14699 -> begin
[]
end))
in (

let reified = (

let uu____14712 = (

let uu____14719 = (

let uu____14720 = (

let uu____14737 = (

let uu____14748 = (

let uu____14759 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____14768 = (

let uu____14779 = (FStar_Syntax_Syntax.as_arg t)
in (uu____14779)::[])
in (uu____14759)::uu____14768))
in (

let uu____14812 = (

let uu____14823 = (

let uu____14834 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____14843 = (

let uu____14854 = (FStar_Syntax_Syntax.as_arg head4)
in (

let uu____14863 = (

let uu____14874 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____14883 = (

let uu____14894 = (FStar_Syntax_Syntax.as_arg body2)
in (uu____14894)::[])
in (uu____14874)::uu____14883))
in (uu____14854)::uu____14863))
in (uu____14834)::uu____14843))
in (FStar_List.append maybe_range_arg uu____14823))
in (FStar_List.append uu____14748 uu____14812)))
in ((bind_inst), (uu____14737)))
in FStar_Syntax_Syntax.Tm_app (uu____14720))
in (FStar_Syntax_Syntax.mk uu____14719))
in (uu____14712 FStar_Pervasives_Native.None rng))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____14975 -> (

let uu____14976 = (FStar_Syntax_Print.term_to_string head0)
in (

let uu____14978 = (FStar_Syntax_Print.term_to_string reified)
in (FStar_Util.print2 "Reified (1) <%s> to %s\n" uu____14976 uu____14978)))));
(

let uu____14981 = (FStar_List.tl stack)
in (norm cfg env uu____14981 reified));
))))))))))
end))
end)))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head_app, args) -> begin
((

let uu____15009 = (FStar_Options.defensive ())
in (match (uu____15009) with
| true -> begin
(

let is_arg_impure = (fun uu____15024 -> (match (uu____15024) with
| (e, q) -> begin
(

let uu____15038 = (

let uu____15039 = (FStar_Syntax_Subst.compress e)
in uu____15039.FStar_Syntax_Syntax.n)
in (match (uu____15038) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t')) -> begin
(

let uu____15055 = (FStar_Syntax_Util.is_pure_effect m1)
in (not (uu____15055)))
end
| uu____15057 -> begin
false
end))
end))
in (

let uu____15059 = (

let uu____15061 = (

let uu____15072 = (FStar_Syntax_Syntax.as_arg head_app)
in (uu____15072)::args)
in (FStar_Util.for_some is_arg_impure uu____15061))
in (match (uu____15059) with
| true -> begin
(

let uu____15098 = (

let uu____15104 = (

let uu____15106 = (FStar_Syntax_Print.term_to_string head3)
in (FStar_Util.format1 "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n" uu____15106))
in ((FStar_Errors.Warning_Defensive), (uu____15104)))
in (FStar_Errors.log_issue head3.FStar_Syntax_Syntax.pos uu____15098))
end
| uu____15110 -> begin
()
end)))
end
| uu____15112 -> begin
()
end));
(

let fallback1 = (fun uu____15119 -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____15123 -> (

let uu____15124 = (FStar_Syntax_Print.term_to_string head0)
in (FStar_Util.print2 "Reified (2) <%s> to %s\n" uu____15124 ""))));
(

let uu____15128 = (FStar_List.tl stack)
in (

let uu____15129 = (FStar_Syntax_Util.mk_reify head3)
in (norm cfg env uu____15128 uu____15129)));
))
in (

let fallback2 = (fun uu____15135 -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____15139 -> (

let uu____15140 = (FStar_Syntax_Print.term_to_string head0)
in (FStar_Util.print2 "Reified (3) <%s> to %s\n" uu____15140 ""))));
(

let uu____15144 = (FStar_List.tl stack)
in (

let uu____15145 = (mk (FStar_Syntax_Syntax.Tm_meta (((head3), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) head0.FStar_Syntax_Syntax.pos)
in (norm cfg env uu____15144 uu____15145)));
))
in (

let uu____15150 = (

let uu____15151 = (FStar_Syntax_Util.un_uinst head_app)
in uu____15151.FStar_Syntax_Syntax.n)
in (match (uu____15150) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let qninfo = (FStar_TypeChecker_Env.lookup_qname cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (

let uu____15157 = (

let uu____15159 = (FStar_TypeChecker_Env.is_action cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (not (uu____15159)))
in (match (uu____15157) with
| true -> begin
(fallback1 ())
end
| uu____15162 -> begin
(

let uu____15164 = (

let uu____15166 = (FStar_TypeChecker_Env.lookup_definition_qninfo cfg.FStar_TypeChecker_Cfg.delta_level fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v qninfo)
in (FStar_Option.isNone uu____15166))
in (match (uu____15164) with
| true -> begin
(fallback2 ())
end
| uu____15178 -> begin
(

let t1 = (

let uu____15183 = (

let uu____15188 = (FStar_Syntax_Util.mk_reify head_app)
in (FStar_Syntax_Syntax.mk_Tm_app uu____15188 args))
in (uu____15183 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let uu____15189 = (FStar_List.tl stack)
in (norm cfg env uu____15189 t1)))
end))
end))))
end
| uu____15190 -> begin
(fallback1 ())
end))));
)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (uu____15192)) -> begin
(do_reify_monadic fallback cfg env stack e m t)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (

let uu____15216 = (closure_as_term cfg env t')
in (reify_lift cfg e msrc mtgt uu____15216))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____15220 -> (

let uu____15221 = (FStar_Syntax_Print.term_to_string lifted)
in (FStar_Util.print1 "Reified lift to (2): %s\n" uu____15221))));
(

let uu____15224 = (FStar_List.tl stack)
in (norm cfg env uu____15224 lifted));
))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____15345 -> (match (uu____15345) with
| (pat, wopt, tm) -> begin
(

let uu____15393 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____15393)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches1)))) head3.FStar_Syntax_Syntax.pos)
in (

let uu____15425 = (FStar_List.tl stack)
in (norm cfg env uu____15425 tm))))
end
| uu____15426 -> begin
(fallback ())
end)));
)));
))
and reify_lift : FStar_TypeChecker_Cfg.cfg  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg e msrc mtgt t -> (

let env = cfg.FStar_TypeChecker_Cfg.tcenv
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____15440 -> (

let uu____15441 = (FStar_Ident.string_of_lid msrc)
in (

let uu____15443 = (FStar_Ident.string_of_lid mtgt)
in (

let uu____15445 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15441 uu____15443 uu____15445))))));
(

let uu____15448 = ((FStar_Syntax_Util.is_pure_effect msrc) || (FStar_Syntax_Util.is_div_effect msrc))
in (match (uu____15448) with
| true -> begin
(

let ed = (

let uu____15452 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv mtgt)
in (FStar_TypeChecker_Env.get_effect_decl env uu____15452))
in (

let uu____15453 = ed.FStar_Syntax_Syntax.return_repr
in (match (uu____15453) with
| (uu____15454, return_repr) -> begin
(

let return_inst = (

let uu____15467 = (

let uu____15468 = (FStar_Syntax_Subst.compress return_repr)
in uu____15468.FStar_Syntax_Syntax.n)
in (match (uu____15467) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (uu____15474)::[]) -> begin
(

let uu____15479 = (

let uu____15486 = (

let uu____15487 = (

let uu____15494 = (

let uu____15495 = (env.FStar_TypeChecker_Env.universe_of env t)
in (uu____15495)::[])
in ((return_tm), (uu____15494)))
in FStar_Syntax_Syntax.Tm_uinst (uu____15487))
in (FStar_Syntax_Syntax.mk uu____15486))
in (uu____15479 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end
| uu____15498 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let uu____15502 = (

let uu____15509 = (

let uu____15510 = (

let uu____15527 = (

let uu____15538 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____15547 = (

let uu____15558 = (FStar_Syntax_Syntax.as_arg e)
in (uu____15558)::[])
in (uu____15538)::uu____15547))
in ((return_inst), (uu____15527)))
in FStar_Syntax_Syntax.Tm_app (uu____15510))
in (FStar_Syntax_Syntax.mk uu____15509))
in (uu____15502 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end)))
end
| uu____15603 -> begin
(

let uu____15605 = (FStar_TypeChecker_Env.monad_leq env msrc mtgt)
in (match (uu____15605) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15608 = (

let uu____15610 = (FStar_Ident.text_of_lid msrc)
in (

let uu____15612 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" uu____15610 uu____15612)))
in (failwith uu____15608))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____15615; FStar_TypeChecker_Env.mtarget = uu____15616; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____15617; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(

let uu____15639 = (

let uu____15641 = (FStar_Ident.text_of_lid msrc)
in (

let uu____15643 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a non-reifiable lift (from %s to %s)" uu____15641 uu____15643)))
in (failwith uu____15639))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____15646; FStar_TypeChecker_Env.mtarget = uu____15647; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____15648; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let uu____15683 = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let uu____15684 = (FStar_Syntax_Util.mk_reify e)
in (lift uu____15683 t FStar_Syntax_Syntax.tun uu____15684)))
end))
end));
)))
and norm_pattern_args : FStar_TypeChecker_Cfg.cfg  ->  env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun uu____15754 -> (match (uu____15754) with
| (a, imp) -> begin
(

let uu____15773 = (norm cfg env [] a)
in ((uu____15773), (imp)))
end))))))
and norm_comp : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____15783 -> (

let uu____15784 = (FStar_Syntax_Print.comp_to_string comp)
in (

let uu____15786 = (FStar_Util.string_of_int (FStar_List.length env))
in (FStar_Util.print2 ">>> %s\nNormComp with with %s env elements" uu____15784 uu____15786)))));
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let t1 = (norm cfg env [] t)
in (

let uopt1 = (match (uopt) with
| FStar_Pervasives_Native.Some (u) -> begin
(

let uu____15812 = (norm_universe cfg env u)
in (FStar_All.pipe_left (fun _15815 -> FStar_Pervasives_Native.Some (_15815)) uu____15812))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let uu___2024_15816 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t1), (uopt1))); FStar_Syntax_Syntax.pos = uu___2024_15816.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___2024_15816.FStar_Syntax_Syntax.vars})))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let t1 = (norm cfg env [] t)
in (

let uopt1 = (match (uopt) with
| FStar_Pervasives_Native.Some (u) -> begin
(

let uu____15838 = (norm_universe cfg env u)
in (FStar_All.pipe_left (fun _15841 -> FStar_Pervasives_Native.Some (_15841)) uu____15838))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let uu___2035_15842 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (((t1), (uopt1))); FStar_Syntax_Syntax.pos = uu___2035_15842.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___2035_15842.FStar_Syntax_Syntax.vars})))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (FStar_List.mapi (fun idx uu____15887 -> (match (uu____15887) with
| (a, i) -> begin
(

let uu____15907 = (norm cfg env [] a)
in ((uu____15907), (i)))
end)))
in (

let effect_args = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___15_15929 -> (match (uu___15_15929) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____15933 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____15933))
end
| f -> begin
f
end))))
in (

let comp_univs = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (

let result_typ = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (

let uu___2052_15941 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ((

let uu___2054_15944 = ct
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___2054_15944.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = effect_args; FStar_Syntax_Syntax.flags = flags})); FStar_Syntax_Syntax.pos = uu___2052_15941.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___2052_15941.FStar_Syntax_Syntax.vars}))))))
end);
))
and norm_binder : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env b -> (

let uu____15948 = b
in (match (uu____15948) with
| (x, imp) -> begin
(

let x1 = (

let uu___2062_15956 = x
in (

let uu____15957 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___2062_15956.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2062_15956.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____15957}))
in (

let imp1 = (match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____15968 = (

let uu____15969 = (closure_as_term cfg env t)
in FStar_Syntax_Syntax.Meta (uu____15969))
in FStar_Pervasives_Native.Some (uu____15968))
end
| i -> begin
i
end)
in ((x1), (imp1))))
end)))
and norm_binders : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let uu____15980 = (FStar_List.fold_left (fun uu____16014 b -> (match (uu____16014) with
| (nbs', env1) -> begin
(

let b1 = (norm_binder cfg env1 b)
in (((b1)::nbs'), ((dummy)::env1)))
end)) (([]), (env)) bs)
in (match (uu____15980) with
| (nbs, uu____16094) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : FStar_TypeChecker_Cfg.cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags = (filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags)
in (

let uu____16126 = (

let uu___2087_16127 = rc
in (

let uu____16128 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___2087_16127.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____16128; FStar_Syntax_Syntax.residual_flags = uu___2087_16127.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____16126)))
end
| uu____16137 -> begin
lopt
end))
and maybe_simplify : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack tm -> (

let tm' = (maybe_simplify_aux cfg env stack tm)
in ((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.b380) with
| true -> begin
(

let uu____16147 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____16149 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n" (match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.simplify) with
| true -> begin
""
end
| uu____16155 -> begin
"NOT "
end) uu____16147 uu____16149)))
end
| uu____16158 -> begin
()
end);
tm';
)))
and norm_cb : FStar_TypeChecker_Cfg.cfg  ->  FStar_Syntax_Embeddings.norm_cb = (fun cfg uu___16_16161 -> (match (uu___16_16161) with
| FStar_Util.Inr (x) -> begin
(norm cfg [] [] x)
end
| FStar_Util.Inl (l) -> begin
(

let uu____16174 = (FStar_Syntax_DsEnv.try_lookup_lid cfg.FStar_TypeChecker_Cfg.tcenv.FStar_TypeChecker_Env.dsenv l)
in (match (uu____16174) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____16178 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____16178))
end))
end))
and maybe_simplify_aux : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack tm -> (

let tm1 = (

let uu____16186 = (norm_cb cfg)
in (reduce_primops uu____16186 cfg env tm))
in (

let uu____16191 = (FStar_All.pipe_left Prims.op_Negation cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.simplify)
in (match (uu____16191) with
| true -> begin
tm1
end
| uu____16196 -> begin
(

let w = (fun t -> (

let uu___2115_16210 = t
in {FStar_Syntax_Syntax.n = uu___2115_16210.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = tm1.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___2115_16210.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (

let uu____16222 = (

let uu____16223 = (FStar_Syntax_Util.unmeta t)
in uu____16223.FStar_Syntax_Syntax.n)
in (match (uu____16222) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_Pervasives_Native.Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid) -> begin
FStar_Pervasives_Native.Some (false)
end
| uu____16235 -> begin
FStar_Pervasives_Native.None
end)))
in (

let rec args_are_binders = (fun args bs -> (match (((args), (bs))) with
| (((t, uu____16299))::args1, ((bv, uu____16302))::bs1) -> begin
(

let uu____16356 = (

let uu____16357 = (FStar_Syntax_Subst.compress t)
in uu____16357.FStar_Syntax_Syntax.n)
in (match (uu____16356) with
| FStar_Syntax_Syntax.Tm_name (bv') -> begin
((FStar_Syntax_Syntax.bv_eq bv bv') && (args_are_binders args1 bs1))
end
| uu____16362 -> begin
false
end))
end
| ([], []) -> begin
true
end
| (uu____16393, uu____16394) -> begin
false
end))
in (

let is_applied = (fun bs t -> ((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____16445 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____16447 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____16445 uu____16447)))
end
| uu____16450 -> begin
()
end);
(

let uu____16452 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____16452) with
| (hd1, args) -> begin
(

let uu____16491 = (

let uu____16492 = (FStar_Syntax_Subst.compress hd1)
in uu____16492.FStar_Syntax_Syntax.n)
in (match (uu____16491) with
| FStar_Syntax_Syntax.Tm_name (bv) when (args_are_binders args bs) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____16500 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____16502 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____16504 = (FStar_Syntax_Print.term_to_string hd1)
in (FStar_Util.print3 "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n" uu____16500 uu____16502 uu____16504))))
end
| uu____16507 -> begin
()
end);
FStar_Pervasives_Native.Some (bv);
)
end
| uu____16509 -> begin
FStar_Pervasives_Native.None
end))
end));
))
in (

let is_applied_maybe_squashed = (fun bs t -> ((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____16527 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____16529 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n" uu____16527 uu____16529)))
end
| uu____16532 -> begin
()
end);
(

let uu____16534 = (FStar_Syntax_Util.is_squash t)
in (match (uu____16534) with
| FStar_Pervasives_Native.Some (uu____16545, t') -> begin
(is_applied bs t')
end
| uu____16557 -> begin
(

let uu____16566 = (FStar_Syntax_Util.is_auto_squash t)
in (match (uu____16566) with
| FStar_Pervasives_Native.Some (uu____16577, t') -> begin
(is_applied bs t')
end
| uu____16589 -> begin
(is_applied bs t)
end))
end));
))
in (

let is_quantified_const = (fun bv phi -> (

let uu____16613 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____16613) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid, ((p, uu____16620))::((q, uu____16622))::[])) when (FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____16665 = (FStar_Syntax_Print.term_to_string p)
in (

let uu____16667 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print2 "WPE> p = (%s); q = (%s)\n" uu____16665 uu____16667)))
end
| uu____16670 -> begin
()
end);
(

let uu____16672 = (FStar_Syntax_Util.destruct_typ_as_formula p)
in (match (uu____16672) with
| FStar_Pervasives_Native.None -> begin
(

let uu____16677 = (

let uu____16678 = (FStar_Syntax_Subst.compress p)
in uu____16678.FStar_Syntax_Syntax.n)
in (match (uu____16677) with
| FStar_Syntax_Syntax.Tm_bvar (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 1\n")
end
| uu____16687 -> begin
()
end);
(

let uu____16689 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (FStar_Syntax_Util.t_true))))::[]) q)
in FStar_Pervasives_Native.Some (uu____16689));
)
end
| uu____16692 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid1, ((p1, uu____16695))::[])) when (FStar_Ident.lid_equals lid1 FStar_Parser_Const.not_lid) -> begin
(

let uu____16720 = (

let uu____16721 = (FStar_Syntax_Subst.compress p1)
in uu____16721.FStar_Syntax_Syntax.n)
in (match (uu____16720) with
| FStar_Syntax_Syntax.Tm_bvar (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 2\n")
end
| uu____16730 -> begin
()
end);
(

let uu____16732 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (FStar_Syntax_Util.t_false))))::[]) q)
in FStar_Pervasives_Native.Some (uu____16732));
)
end
| uu____16735 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (bs, pats, phi1)) -> begin
(

let uu____16739 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____16739) with
| FStar_Pervasives_Native.None -> begin
(

let uu____16744 = (is_applied_maybe_squashed bs phi1)
in (match (uu____16744) with
| FStar_Pervasives_Native.Some (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 3\n")
end
| uu____16753 -> begin
()
end);
(

let ftrue = (FStar_Syntax_Util.abs bs FStar_Syntax_Util.t_true (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let uu____16758 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (ftrue))))::[]) q)
in FStar_Pervasives_Native.Some (uu____16758)));
)
end
| uu____16761 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid1, ((p1, uu____16766))::[])) when (FStar_Ident.lid_equals lid1 FStar_Parser_Const.not_lid) -> begin
(

let uu____16791 = (is_applied_maybe_squashed bs p1)
in (match (uu____16791) with
| FStar_Pervasives_Native.Some (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 4\n")
end
| uu____16800 -> begin
()
end);
(

let ffalse = (FStar_Syntax_Util.abs bs FStar_Syntax_Util.t_false (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let uu____16805 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (ffalse))))::[]) q)
in FStar_Pervasives_Native.Some (uu____16805)));
)
end
| uu____16808 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____16811 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____16814 -> begin
FStar_Pervasives_Native.None
end));
)
end
| uu____16817 -> begin
FStar_Pervasives_Native.None
end)))
in (

let is_forall_const = (fun phi -> (

let uu____16830 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____16830) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (((bv, uu____16836))::[], uu____16837, phi')) -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____16857 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____16859 = (FStar_Syntax_Print.term_to_string phi')
in (FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____16857 uu____16859)))
end
| uu____16862 -> begin
()
end);
(is_quantified_const bv phi');
)
end
| uu____16864 -> begin
FStar_Pervasives_Native.None
end)))
in (

let is_const_match = (fun phi -> (

let uu____16879 = (

let uu____16880 = (FStar_Syntax_Subst.compress phi)
in uu____16880.FStar_Syntax_Syntax.n)
in (match (uu____16879) with
| FStar_Syntax_Syntax.Tm_match (uu____16886, (br)::brs) -> begin
(

let uu____16953 = br
in (match (uu____16953) with
| (uu____16971, uu____16972, e) -> begin
(

let r = (

let uu____16994 = (simp_t e)
in (match (uu____16994) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let uu____17006 = (FStar_List.for_all (fun uu____17025 -> (match (uu____17025) with
| (uu____17039, uu____17040, e') -> begin
(

let uu____17054 = (simp_t e')
in (Prims.op_Equality uu____17054 (FStar_Pervasives_Native.Some (b))))
end)) brs)
in (match (uu____17006) with
| true -> begin
FStar_Pervasives_Native.Some (b)
end
| uu____17067 -> begin
FStar_Pervasives_Native.None
end))
end))
in r)
end))
end
| uu____17070 -> begin
FStar_Pervasives_Native.None
end)))
in (

let maybe_auto_squash = (fun t -> (

let uu____17080 = (FStar_Syntax_Util.is_sub_singleton t)
in (match (uu____17080) with
| true -> begin
t
end
| uu____17085 -> begin
(FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t)
end)))
in (

let squashed_head_un_auto_squash_args = (fun t -> (

let maybe_un_auto_squash_arg = (fun uu____17118 -> (match (uu____17118) with
| (t1, q) -> begin
(

let uu____17139 = (FStar_Syntax_Util.is_auto_squash t1)
in (match (uu____17139) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t2) -> begin
((t2), (q))
end
| uu____17171 -> begin
((t1), (q))
end))
end))
in (

let uu____17184 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____17184) with
| (head1, args) -> begin
(

let args1 = (FStar_List.map maybe_un_auto_squash_arg args)
in (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))))
in (

let rec clearly_inhabited = (fun ty -> (

let uu____17264 = (

let uu____17265 = (FStar_Syntax_Util.unmeta ty)
in uu____17265.FStar_Syntax_Syntax.n)
in (match (uu____17264) with
| FStar_Syntax_Syntax.Tm_uinst (t, uu____17270) -> begin
(clearly_inhabited t)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____17275, c) -> begin
(clearly_inhabited (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in ((((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)))
end
| uu____17299 -> begin
false
end)))
in (

let simplify1 = (fun arg -> (

let uu____17332 = (simp_t (FStar_Pervasives_Native.fst arg))
in ((uu____17332), (arg))))
in (

let uu____17347 = (is_forall_const tm1)
in (match (uu____17347) with
| FStar_Pervasives_Native.Some (tm') -> begin
((match (cfg.FStar_TypeChecker_Cfg.debug.FStar_TypeChecker_Cfg.wpe) with
| true -> begin
(

let uu____17353 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____17355 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "WPE> %s ~> %s\n" uu____17353 uu____17355)))
end
| uu____17358 -> begin
()
end);
(

let uu____17360 = (norm cfg env [] tm')
in (maybe_simplify_aux cfg env stack uu____17360));
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____17361 = (

let uu____17362 = (FStar_Syntax_Subst.compress tm1)
in uu____17362.FStar_Syntax_Syntax.n)
in (match (uu____17361) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____17366; FStar_Syntax_Syntax.vars = uu____17367}, uu____17368); FStar_Syntax_Syntax.pos = uu____17369; FStar_Syntax_Syntax.vars = uu____17370}, args) -> begin
(

let uu____17400 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____17400) with
| true -> begin
(

let uu____17403 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____17403) with
| ((FStar_Pervasives_Native.Some (true), uu____17461))::((uu____17462, (arg, uu____17464)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____17537, (arg, uu____17539)))::((FStar_Pervasives_Native.Some (true), uu____17540))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (false), uu____17613))::(uu____17614)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____17684)::((FStar_Pervasives_Native.Some (false), uu____17685))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____17755 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____17771 -> begin
(

let uu____17773 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____17773) with
| true -> begin
(

let uu____17776 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____17776) with
| ((FStar_Pervasives_Native.Some (true), uu____17834))::(uu____17835)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____17905)::((FStar_Pervasives_Native.Some (true), uu____17906))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____17976))::((uu____17977, (arg, uu____17979)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____18052, (arg, uu____18054)))::((FStar_Pervasives_Native.Some (false), uu____18055))::[] -> begin
(maybe_auto_squash arg)
end
| uu____18128 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____18144 -> begin
(

let uu____18146 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____18146) with
| true -> begin
(

let uu____18149 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____18149) with
| (uu____18207)::((FStar_Pervasives_Native.Some (true), uu____18208))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____18278))::(uu____18279)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____18349))::((uu____18350, (arg, uu____18352)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____18425, (p, uu____18427)))::((uu____18428, (q, uu____18430)))::[] -> begin
(

let uu____18502 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____18502) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____18505 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____18507 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____18523 -> begin
(

let uu____18525 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)
in (match (uu____18525) with
| true -> begin
(

let uu____18528 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____18528) with
| ((FStar_Pervasives_Native.Some (true), uu____18586))::((FStar_Pervasives_Native.Some (true), uu____18587))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____18661))::((FStar_Pervasives_Native.Some (false), uu____18662))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____18736))::((FStar_Pervasives_Native.Some (false), uu____18737))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____18811))::((FStar_Pervasives_Native.Some (true), uu____18812))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((uu____18886, (arg, uu____18888)))::((FStar_Pervasives_Native.Some (true), uu____18889))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (true), uu____18962))::((uu____18963, (arg, uu____18965)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____19038, (arg, uu____19040)))::((FStar_Pervasives_Native.Some (false), uu____19041))::[] -> begin
(

let uu____19114 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____19114))
end
| ((FStar_Pervasives_Native.Some (false), uu____19115))::((uu____19116, (arg, uu____19118)))::[] -> begin
(

let uu____19191 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____19191))
end
| ((uu____19192, (p, uu____19194)))::((uu____19195, (q, uu____19197)))::[] -> begin
(

let uu____19269 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____19269) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____19272 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19274 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19290 -> begin
(

let uu____19292 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____19292) with
| true -> begin
(

let uu____19295 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____19295) with
| ((FStar_Pervasives_Native.Some (true), uu____19353))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____19397))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____19441 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19457 -> begin
(

let uu____19459 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____19459) with
| true -> begin
(match (args) with
| ((t, uu____19463))::[] -> begin
(

let uu____19488 = (

let uu____19489 = (FStar_Syntax_Subst.compress t)
in uu____19489.FStar_Syntax_Syntax.n)
in (match (uu____19488) with
| FStar_Syntax_Syntax.Tm_abs ((uu____19492)::[], body, uu____19494) -> begin
(

let uu____19529 = (simp_t body)
in (match (uu____19529) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____19535 -> begin
tm1
end))
end
| uu____19539 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____19541))))::((t, uu____19543))::[] -> begin
(

let uu____19583 = (

let uu____19584 = (FStar_Syntax_Subst.compress t)
in uu____19584.FStar_Syntax_Syntax.n)
in (match (uu____19583) with
| FStar_Syntax_Syntax.Tm_abs ((uu____19587)::[], body, uu____19589) -> begin
(

let uu____19624 = (simp_t body)
in (match (uu____19624) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| FStar_Pervasives_Native.Some (false) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____19632 -> begin
tm1
end))
end
| uu____19636 -> begin
tm1
end))
end
| uu____19637 -> begin
tm1
end)
end
| uu____19648 -> begin
(

let uu____19650 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____19650) with
| true -> begin
(match (args) with
| ((t, uu____19654))::[] -> begin
(

let uu____19679 = (

let uu____19680 = (FStar_Syntax_Subst.compress t)
in uu____19680.FStar_Syntax_Syntax.n)
in (match (uu____19679) with
| FStar_Syntax_Syntax.Tm_abs ((uu____19683)::[], body, uu____19685) -> begin
(

let uu____19720 = (simp_t body)
in (match (uu____19720) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____19726 -> begin
tm1
end))
end
| uu____19730 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____19732))))::((t, uu____19734))::[] -> begin
(

let uu____19774 = (

let uu____19775 = (FStar_Syntax_Subst.compress t)
in uu____19775.FStar_Syntax_Syntax.n)
in (match (uu____19774) with
| FStar_Syntax_Syntax.Tm_abs ((uu____19778)::[], body, uu____19780) -> begin
(

let uu____19815 = (simp_t body)
in (match (uu____19815) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| FStar_Pervasives_Native.Some (true) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____19823 -> begin
tm1
end))
end
| uu____19827 -> begin
tm1
end))
end
| uu____19828 -> begin
tm1
end)
end
| uu____19839 -> begin
(

let uu____19841 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
in (match (uu____19841) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____19844; FStar_Syntax_Syntax.vars = uu____19845}, uu____19846))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____19872; FStar_Syntax_Syntax.vars = uu____19873}, uu____19874))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____19900 -> begin
tm1
end)
end
| uu____19911 -> begin
(

let uu____19913 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.haseq_lid)
in (match (uu____19913) with
| true -> begin
(

let t_has_eq_for_sure = (fun t -> (

let haseq_lids = (FStar_Parser_Const.int_lid)::(FStar_Parser_Const.bool_lid)::(FStar_Parser_Const.unit_lid)::(FStar_Parser_Const.string_lid)::[]
in (

let uu____19927 = (

let uu____19928 = (FStar_Syntax_Subst.compress t)
in uu____19928.FStar_Syntax_Syntax.n)
in (match (uu____19927) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (FStar_All.pipe_right haseq_lids (FStar_List.existsb (fun l -> (FStar_Syntax_Syntax.fv_eq_lid fv1 l)))) -> begin
true
end
| uu____19939 -> begin
false
end))))
in (match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "1"))) with
| true -> begin
(

let t = (

let uu____19953 = (FStar_All.pipe_right args FStar_List.hd)
in (FStar_All.pipe_right uu____19953 FStar_Pervasives_Native.fst))
in (

let uu____19992 = (FStar_All.pipe_right t t_has_eq_for_sure)
in (match (uu____19992) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____19996 -> begin
(

let uu____19998 = (

let uu____19999 = (FStar_Syntax_Subst.compress t)
in uu____19999.FStar_Syntax_Syntax.n)
in (match (uu____19998) with
| FStar_Syntax_Syntax.Tm_refine (uu____20002) -> begin
(

let t1 = (FStar_Syntax_Util.unrefine t)
in (

let uu____20010 = (FStar_All.pipe_right t1 t_has_eq_for_sure)
in (match (uu____20010) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20014 -> begin
(

let haseq_tm = (

let uu____20019 = (

let uu____20020 = (FStar_Syntax_Subst.compress tm1)
in uu____20020.FStar_Syntax_Syntax.n)
in (match (uu____20019) with
| FStar_Syntax_Syntax.Tm_app (hd1, uu____20026) -> begin
hd1
end
| uu____20051 -> begin
(failwith "Impossible! We have already checked that this is a Tm_app")
end))
in (

let uu____20055 = (

let uu____20066 = (FStar_All.pipe_right t1 FStar_Syntax_Syntax.as_arg)
in (uu____20066)::[])
in (FStar_Syntax_Util.mk_app haseq_tm uu____20055)))
end)))
end
| uu____20099 -> begin
tm1
end))
end)))
end
| uu____20100 -> begin
tm1
end))
end
| uu____20102 -> begin
(

let uu____20104 = (FStar_Syntax_Util.is_auto_squash tm1)
in (match (uu____20104) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t) when (FStar_Syntax_Util.is_sub_singleton t) -> begin
t
end
| uu____20124 -> begin
(

let uu____20133 = (

let uu____20140 = (norm_cb cfg)
in (reduce_equality uu____20140 cfg env))
in (uu____20133 tm1))
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
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____20146; FStar_Syntax_Syntax.vars = uu____20147}, args) -> begin
(

let uu____20173 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____20173) with
| true -> begin
(

let uu____20176 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____20176) with
| ((FStar_Pervasives_Native.Some (true), uu____20234))::((uu____20235, (arg, uu____20237)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____20310, (arg, uu____20312)))::((FStar_Pervasives_Native.Some (true), uu____20313))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (false), uu____20386))::(uu____20387)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____20457)::((FStar_Pervasives_Native.Some (false), uu____20458))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____20528 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20544 -> begin
(

let uu____20546 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____20546) with
| true -> begin
(

let uu____20549 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____20549) with
| ((FStar_Pervasives_Native.Some (true), uu____20607))::(uu____20608)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____20678)::((FStar_Pervasives_Native.Some (true), uu____20679))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____20749))::((uu____20750, (arg, uu____20752)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____20825, (arg, uu____20827)))::((FStar_Pervasives_Native.Some (false), uu____20828))::[] -> begin
(maybe_auto_squash arg)
end
| uu____20901 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20917 -> begin
(

let uu____20919 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____20919) with
| true -> begin
(

let uu____20922 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____20922) with
| (uu____20980)::((FStar_Pervasives_Native.Some (true), uu____20981))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____21051))::(uu____21052)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____21122))::((uu____21123, (arg, uu____21125)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____21198, (p, uu____21200)))::((uu____21201, (q, uu____21203)))::[] -> begin
(

let uu____21275 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____21275) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____21278 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____21280 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____21296 -> begin
(

let uu____21298 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)
in (match (uu____21298) with
| true -> begin
(

let uu____21301 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____21301) with
| ((FStar_Pervasives_Native.Some (true), uu____21359))::((FStar_Pervasives_Native.Some (true), uu____21360))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____21434))::((FStar_Pervasives_Native.Some (false), uu____21435))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____21509))::((FStar_Pervasives_Native.Some (false), uu____21510))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____21584))::((FStar_Pervasives_Native.Some (true), uu____21585))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((uu____21659, (arg, uu____21661)))::((FStar_Pervasives_Native.Some (true), uu____21662))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (true), uu____21735))::((uu____21736, (arg, uu____21738)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____21811, (arg, uu____21813)))::((FStar_Pervasives_Native.Some (false), uu____21814))::[] -> begin
(

let uu____21887 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____21887))
end
| ((FStar_Pervasives_Native.Some (false), uu____21888))::((uu____21889, (arg, uu____21891)))::[] -> begin
(

let uu____21964 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____21964))
end
| ((uu____21965, (p, uu____21967)))::((uu____21968, (q, uu____21970)))::[] -> begin
(

let uu____22042 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____22042) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22045 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____22047 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____22063 -> begin
(

let uu____22065 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____22065) with
| true -> begin
(

let uu____22068 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____22068) with
| ((FStar_Pervasives_Native.Some (true), uu____22126))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____22170))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22214 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____22230 -> begin
(

let uu____22232 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____22232) with
| true -> begin
(match (args) with
| ((t, uu____22236))::[] -> begin
(

let uu____22261 = (

let uu____22262 = (FStar_Syntax_Subst.compress t)
in uu____22262.FStar_Syntax_Syntax.n)
in (match (uu____22261) with
| FStar_Syntax_Syntax.Tm_abs ((uu____22265)::[], body, uu____22267) -> begin
(

let uu____22302 = (simp_t body)
in (match (uu____22302) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22308 -> begin
tm1
end))
end
| uu____22312 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____22314))))::((t, uu____22316))::[] -> begin
(

let uu____22356 = (

let uu____22357 = (FStar_Syntax_Subst.compress t)
in uu____22357.FStar_Syntax_Syntax.n)
in (match (uu____22356) with
| FStar_Syntax_Syntax.Tm_abs ((uu____22360)::[], body, uu____22362) -> begin
(

let uu____22397 = (simp_t body)
in (match (uu____22397) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| FStar_Pervasives_Native.Some (false) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____22405 -> begin
tm1
end))
end
| uu____22409 -> begin
tm1
end))
end
| uu____22410 -> begin
tm1
end)
end
| uu____22421 -> begin
(

let uu____22423 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____22423) with
| true -> begin
(match (args) with
| ((t, uu____22427))::[] -> begin
(

let uu____22452 = (

let uu____22453 = (FStar_Syntax_Subst.compress t)
in uu____22453.FStar_Syntax_Syntax.n)
in (match (uu____22452) with
| FStar_Syntax_Syntax.Tm_abs ((uu____22456)::[], body, uu____22458) -> begin
(

let uu____22493 = (simp_t body)
in (match (uu____22493) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____22499 -> begin
tm1
end))
end
| uu____22503 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____22505))))::((t, uu____22507))::[] -> begin
(

let uu____22547 = (

let uu____22548 = (FStar_Syntax_Subst.compress t)
in uu____22548.FStar_Syntax_Syntax.n)
in (match (uu____22547) with
| FStar_Syntax_Syntax.Tm_abs ((uu____22551)::[], body, uu____22553) -> begin
(

let uu____22588 = (simp_t body)
in (match (uu____22588) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| FStar_Pervasives_Native.Some (true) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22596 -> begin
tm1
end))
end
| uu____22600 -> begin
tm1
end))
end
| uu____22601 -> begin
tm1
end)
end
| uu____22612 -> begin
(

let uu____22614 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
in (match (uu____22614) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____22617; FStar_Syntax_Syntax.vars = uu____22618}, uu____22619))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____22645; FStar_Syntax_Syntax.vars = uu____22646}, uu____22647))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____22673 -> begin
tm1
end)
end
| uu____22684 -> begin
(

let uu____22686 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.haseq_lid)
in (match (uu____22686) with
| true -> begin
(

let t_has_eq_for_sure = (fun t -> (

let haseq_lids = (FStar_Parser_Const.int_lid)::(FStar_Parser_Const.bool_lid)::(FStar_Parser_Const.unit_lid)::(FStar_Parser_Const.string_lid)::[]
in (

let uu____22700 = (

let uu____22701 = (FStar_Syntax_Subst.compress t)
in uu____22701.FStar_Syntax_Syntax.n)
in (match (uu____22700) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (FStar_All.pipe_right haseq_lids (FStar_List.existsb (fun l -> (FStar_Syntax_Syntax.fv_eq_lid fv1 l)))) -> begin
true
end
| uu____22712 -> begin
false
end))))
in (match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "1"))) with
| true -> begin
(

let t = (

let uu____22726 = (FStar_All.pipe_right args FStar_List.hd)
in (FStar_All.pipe_right uu____22726 FStar_Pervasives_Native.fst))
in (

let uu____22761 = (FStar_All.pipe_right t t_has_eq_for_sure)
in (match (uu____22761) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22765 -> begin
(

let uu____22767 = (

let uu____22768 = (FStar_Syntax_Subst.compress t)
in uu____22768.FStar_Syntax_Syntax.n)
in (match (uu____22767) with
| FStar_Syntax_Syntax.Tm_refine (uu____22771) -> begin
(

let t1 = (FStar_Syntax_Util.unrefine t)
in (

let uu____22779 = (FStar_All.pipe_right t1 t_has_eq_for_sure)
in (match (uu____22779) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22783 -> begin
(

let haseq_tm = (

let uu____22788 = (

let uu____22789 = (FStar_Syntax_Subst.compress tm1)
in uu____22789.FStar_Syntax_Syntax.n)
in (match (uu____22788) with
| FStar_Syntax_Syntax.Tm_app (hd1, uu____22795) -> begin
hd1
end
| uu____22820 -> begin
(failwith "Impossible! We have already checked that this is a Tm_app")
end))
in (

let uu____22824 = (

let uu____22835 = (FStar_All.pipe_right t1 FStar_Syntax_Syntax.as_arg)
in (uu____22835)::[])
in (FStar_Syntax_Util.mk_app haseq_tm uu____22824)))
end)))
end
| uu____22868 -> begin
tm1
end))
end)))
end
| uu____22869 -> begin
tm1
end))
end
| uu____22871 -> begin
(

let uu____22873 = (FStar_Syntax_Util.is_auto_squash tm1)
in (match (uu____22873) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t) when (FStar_Syntax_Util.is_sub_singleton t) -> begin
t
end
| uu____22893 -> begin
(

let uu____22902 = (

let uu____22909 = (norm_cb cfg)
in (reduce_equality uu____22909 cfg env))
in (uu____22902 tm1))
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

let uu____22920 = (simp_t t)
in (match (uu____22920) with
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
| FStar_Syntax_Syntax.Tm_match (uu____22929) -> begin
(

let uu____22952 = (is_const_match tm1)
in (match (uu____22952) with
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
| uu____22961 -> begin
tm1
end))
end))))))))))))))
end))))
and rebuild : FStar_TypeChecker_Cfg.cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____22971 -> ((

let uu____22973 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____22975 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____22977 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____22985 = (

let uu____22987 = (

let uu____22990 = (firstn (Prims.parse_int "4") stack)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____22990))
in (stack_to_string uu____22987))
in (FStar_Util.print4 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n" uu____22973 uu____22975 uu____22977 uu____22985)))));
(

let uu____23015 = (FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv (FStar_Options.Other ("NormRebuild")))
in (match (uu____23015) with
| true -> begin
(

let uu____23019 = (FStar_Syntax_Util.unbound_variables t)
in (match (uu____23019) with
| [] -> begin
()
end
| bvs -> begin
((

let uu____23026 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____23028 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____23030 = (

let uu____23032 = (FStar_All.pipe_right bvs (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right uu____23032 (FStar_String.concat ", ")))
in (FStar_Util.print3 "!!! Rebuild (%s) %s, free vars=%s\n" uu____23026 uu____23028 uu____23030))));
(failwith "DIE!");
)
end))
end
| uu____23049 -> begin
()
end));
)));
(

let f_opt = (is_fext_on_domain t)
in (

let uu____23054 = ((FStar_All.pipe_right f_opt FStar_Util.is_some) && (match (stack) with
| (Arg (uu____23062))::uu____23063 -> begin
true
end
| uu____23073 -> begin
false
end))
in (match (uu____23054) with
| true -> begin
(

let uu____23076 = (FStar_All.pipe_right f_opt FStar_Util.must)
in (FStar_All.pipe_right uu____23076 (norm cfg env stack)))
end
| uu____23079 -> begin
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

let uu____23090 = (

let uu____23092 = (

let uu____23094 = (FStar_Util.time_diff time_then time_now)
in (FStar_Pervasives_Native.snd uu____23094))
in (FStar_Util.string_of_int uu____23092))
in (

let uu____23101 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____23103 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized term (%s ms) %s\n\tto term %s\n" uu____23090 uu____23101 uu____23103)))))
end
| uu____23106 -> begin
()
end);
(rebuild cfg env stack1 t1);
)
end
| (Cfg (cfg1))::stack1 -> begin
(rebuild cfg1 env stack1 t1)
end
| (Meta (uu____23112, m, r))::stack1 -> begin
(

let t2 = (mk (FStar_Syntax_Syntax.Tm_meta (((t1), (m)))) r)
in (rebuild cfg env stack1 t2))
end
| (MemoLazy (r))::stack1 -> begin
((set_memo cfg r ((env), (t1)));
(FStar_TypeChecker_Cfg.log cfg (fun uu____23141 -> (

let uu____23142 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____23142))));
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

let uu____23185 = (

let uu___2744_23186 = (FStar_Syntax_Util.abs bs1 t1 lopt1)
in {FStar_Syntax_Syntax.n = uu___2744_23186.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___2744_23186.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack1 uu____23185))))
end
| (Arg (Univ (uu____23189), uu____23190, uu____23191))::uu____23192 -> begin
(failwith "Impossible")
end
| (Arg (Dummy, uu____23196, uu____23197))::uu____23198 -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack1 -> begin
(

let t2 = (FStar_Syntax_Syntax.mk_Tm_uinst t1 us)
in (rebuild cfg env stack1 t2))
end
| (Arg (Clos (env_arg, tm, uu____23214, uu____23215), aq, r))::stack1 when (

let uu____23267 = (head_of t1)
in (FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____23267)) -> begin
(

let t2 = (

let uu____23271 = (

let uu____23276 = (

let uu____23277 = (closure_as_term cfg env_arg tm)
in ((uu____23277), (aq)))
in (FStar_Syntax_Syntax.extend_app t1 uu____23276))
in (uu____23271 FStar_Pervasives_Native.None r))
in (rebuild cfg env stack1 t2))
end
| (Arg (Clos (env_arg, tm, m, uu____23287), aq, r))::stack1 -> begin
((FStar_TypeChecker_Cfg.log cfg (fun uu____23342 -> (

let uu____23343 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" uu____23343))));
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
| uu____23356 -> begin
(

let stack2 = (App (((env), (t1), (aq), (r))))::stack1
in (norm cfg env_arg stack2 tm))
end)
end
| uu____23361 -> begin
(

let uu____23363 = (FStar_ST.op_Bang m)
in (match (uu____23363) with
| FStar_Pervasives_Native.None -> begin
(match (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.hnf) with
| true -> begin
(

let arg = (closure_as_term cfg env_arg tm)
in (

let t2 = (FStar_Syntax_Syntax.extend_app t1 ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack1 t2)))
end
| uu____23446 -> begin
(

let stack2 = (MemoLazy (m))::(App (((env), (t1), (aq), (r))))::stack1
in (norm cfg env_arg stack2 tm))
end)
end
| FStar_Pervasives_Native.Some (uu____23451, a) -> begin
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

let fallback = (fun msg uu____23507 -> ((FStar_TypeChecker_Cfg.log cfg (fun uu____23512 -> (

let uu____23513 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not reifying%s: %s\n" msg uu____23513))));
(

let t2 = (FStar_Syntax_Syntax.extend_app head1 ((t1), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack' t2));
))
in (

let uu____23523 = (

let uu____23524 = (FStar_Syntax_Subst.compress t1)
in uu____23524.FStar_Syntax_Syntax.n)
in (match (uu____23523) with
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic (m, ty)) -> begin
(do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty)
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, ty)) -> begin
(

let lifted = (

let uu____23552 = (closure_as_term cfg env1 ty)
in (reify_lift cfg t2 msrc mtgt uu____23552))
in ((FStar_TypeChecker_Cfg.log cfg (fun uu____23556 -> (

let uu____23557 = (FStar_Syntax_Print.term_to_string lifted)
in (FStar_Util.print1 "Reified lift to (1): %s\n" uu____23557))));
(

let uu____23560 = (FStar_List.tl stack)
in (norm cfg env1 uu____23560 lifted));
))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____23561)); FStar_Syntax_Syntax.pos = uu____23562; FStar_Syntax_Syntax.vars = uu____23563}, ((e, uu____23565))::[]) -> begin
(norm cfg env1 stack' e)
end
| FStar_Syntax_Syntax.Tm_app (uu____23604) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.primops -> begin
(

let uu____23621 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____23621) with
| (hd1, args) -> begin
(

let uu____23664 = (

let uu____23665 = (FStar_Syntax_Util.un_uinst hd1)
in uu____23665.FStar_Syntax_Syntax.n)
in (match (uu____23664) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____23669 = (FStar_TypeChecker_Cfg.find_prim_step cfg fv)
in (match (uu____23669) with
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Cfg.name = uu____23672; FStar_TypeChecker_Cfg.arity = uu____23673; FStar_TypeChecker_Cfg.univ_arity = uu____23674; FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.Some (n1); FStar_TypeChecker_Cfg.strong_reduction_ok = uu____23676; FStar_TypeChecker_Cfg.requires_binder_substitution = uu____23677; FStar_TypeChecker_Cfg.interpretation = uu____23678; FStar_TypeChecker_Cfg.interpretation_nbe = uu____23679}) when (Prims.op_Equality (FStar_List.length args) n1) -> begin
(norm cfg env1 stack' t1)
end
| uu____23715 -> begin
(fallback " (3)" ())
end))
end
| uu____23719 -> begin
(fallback " (4)" ())
end))
end))
end
| uu____23721 -> begin
(fallback " (2)" ())
end))))
end
| (App (env1, head1, aq, r))::stack1 -> begin
(

let t2 = (FStar_Syntax_Syntax.extend_app head1 ((t1), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack1 t2))
end
| (Match (env', branches, cfg1, r))::stack1 -> begin
((FStar_TypeChecker_Cfg.log cfg1 (fun uu____23747 -> (

let uu____23748 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" uu____23748))));
(

let scrutinee_env = env
in (

let env1 = env'
in (

let scrutinee = t1
in (

let norm_and_rebuild_match = (fun uu____23759 -> ((FStar_TypeChecker_Cfg.log cfg1 (fun uu____23764 -> (

let uu____23765 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____23767 = (

let uu____23769 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____23799 -> (match (uu____23799) with
| (p, uu____23810, uu____23811) -> begin
(FStar_Syntax_Print.pat_to_string p)
end))))
in (FStar_All.pipe_right uu____23769 (FStar_String.concat "\n\t")))
in (FStar_Util.print2 "match is irreducible: scrutinee=%s\nbranches=%s\n" uu____23765 uu____23767)))));
(

let whnf = (cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak || cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.hnf)
in (

let cfg_exclude_zeta = (

let new_delta = (FStar_All.pipe_right cfg1.FStar_TypeChecker_Cfg.delta_level (FStar_List.filter (fun uu___17_23833 -> (match (uu___17_23833) with
| FStar_TypeChecker_Env.InliningDelta -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| uu____23837 -> begin
false
end))))
in (

let steps = (

let uu___2912_23840 = cfg1.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___2912_23840.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___2912_23840.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = false; FStar_TypeChecker_Cfg.weak = uu___2912_23840.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___2912_23840.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___2912_23840.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___2912_23840.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_only = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_fully = uu___2912_23840.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.unfold_tac = false; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___2912_23840.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___2912_23840.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___2912_23840.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___2912_23840.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___2912_23840.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___2912_23840.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___2912_23840.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___2912_23840.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___2912_23840.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___2912_23840.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___2912_23840.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___2912_23840.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___2912_23840.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___2912_23840.FStar_TypeChecker_Cfg.for_extraction})
in (

let uu___2915_23847 = cfg1
in {FStar_TypeChecker_Cfg.steps = steps; FStar_TypeChecker_Cfg.tcenv = uu___2915_23847.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___2915_23847.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = new_delta; FStar_TypeChecker_Cfg.primitive_steps = uu___2915_23847.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = true; FStar_TypeChecker_Cfg.memoize_lazy = uu___2915_23847.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___2915_23847.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___2915_23847.FStar_TypeChecker_Cfg.reifying})))
in (

let norm_or_whnf = (fun env2 t2 -> (match (whnf) with
| true -> begin
(closure_as_term cfg_exclude_zeta env2 t2)
end
| uu____23861 -> begin
(norm cfg_exclude_zeta env2 [] t2)
end))
in (

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____23922) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____23953 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____24042 uu____24043 -> (match (((uu____24042), (uu____24043))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____24193 = (norm_pat env3 p1)
in (match (uu____24193) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____23953) with
| (pats1, env3) -> begin
(((

let uu___2943_24363 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___2943_24363.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___2947_24384 = x
in (

let uu____24385 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___2947_24384.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2947_24384.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____24385}))
in (((

let uu___2950_24399 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___2950_24399.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___2954_24410 = x
in (

let uu____24411 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___2954_24410.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2954_24410.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____24411}))
in (((

let uu___2957_24425 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___2957_24425.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t2) -> begin
(

let x1 = (

let uu___2963_24441 = x
in (

let uu____24442 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___2963_24441.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2963_24441.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____24442}))
in (

let t3 = (norm_or_whnf env2 t2)
in (((

let uu___2967_24457 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t3))); FStar_Syntax_Syntax.p = uu___2967_24457.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let branches1 = (match (env1) with
| [] when whnf -> begin
branches
end
| uu____24501 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch1 -> (

let uu____24531 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____24531) with
| (p, wopt, e) -> begin
(

let uu____24551 = (norm_pat env1 p)
in (match (uu____24551) with
| (p1, env2) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____24606 = (norm_or_whnf env2 w)
in FStar_Pervasives_Native.Some (uu____24606))
end)
in (

let e1 = (norm_or_whnf env2 e)
in (FStar_Syntax_Util.branch ((p1), (wopt1), (e1)))))
end))
end)))))
end)
in (

let scrutinee1 = (

let uu____24623 = ((((cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.iota && (not (cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weak))) && (not (cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.compress_uvars))) && cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee) && (maybe_weakly_reduced scrutinee))
in (match (uu____24623) with
| true -> begin
(norm (

let uu___2986_24630 = cfg1
in {FStar_TypeChecker_Cfg.steps = (

let uu___2988_24633 = cfg1.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___2988_24633.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___2988_24633.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___2988_24633.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___2988_24633.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___2988_24633.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___2988_24633.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___2988_24633.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___2988_24633.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___2988_24633.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___2988_24633.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___2988_24633.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___2988_24633.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___2988_24633.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___2988_24633.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___2988_24633.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___2988_24633.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___2988_24633.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___2988_24633.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___2988_24633.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___2988_24633.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___2988_24633.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___2988_24633.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___2988_24633.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = false; FStar_TypeChecker_Cfg.nbe_step = uu___2988_24633.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___2988_24633.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___2986_24630.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___2986_24630.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___2986_24630.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___2986_24630.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___2986_24630.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___2986_24630.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___2986_24630.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___2986_24630.FStar_TypeChecker_Cfg.reifying}) scrutinee_env [] scrutinee)
end
| uu____24635 -> begin
scrutinee
end))
in (

let uu____24637 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee1), (branches1)))) r)
in (rebuild cfg1 env1 stack1 uu____24637))))))));
))
in (

let rec is_cons = (fun head1 -> (

let uu____24663 = (

let uu____24664 = (FStar_Syntax_Subst.compress head1)
in uu____24664.FStar_Syntax_Syntax.n)
in (match (uu____24663) with
| FStar_Syntax_Syntax.Tm_uinst (h, uu____24669) -> begin
(is_cons h)
end
| FStar_Syntax_Syntax.Tm_constant (uu____24674) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____24676; FStar_Syntax_Syntax.fv_delta = uu____24677; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____24679; FStar_Syntax_Syntax.fv_delta = uu____24680; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____24681))}) -> begin
true
end
| uu____24689 -> begin
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

let uu____24858 = (FStar_Syntax_Util.head_and_args scrutinee2)
in (match (uu____24858) with
| (head1, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____24955) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (FStar_Const.eq_const s s') -> begin
FStar_Util.Inl ([])
end
| uu____24997 -> begin
(

let uu____24998 = (

let uu____25000 = (is_cons head1)
in (not (uu____25000)))
in FStar_Util.Inr (uu____24998))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let uu____25029 = (

let uu____25030 = (FStar_Syntax_Util.un_uinst head1)
in uu____25030.FStar_Syntax_Syntax.n)
in (match (uu____25029) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| uu____25049 -> begin
(

let uu____25050 = (

let uu____25052 = (is_cons head1)
in (not (uu____25052)))
in FStar_Util.Inr (uu____25050))
end))
end)
end)))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t2, uu____25143))::rest_a, ((p1, uu____25146))::rest_p) -> begin
(

let uu____25205 = (matches_pat t2 p1)
in (match (uu____25205) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____25258 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee1 p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p1, wopt, b))::rest -> begin
(

let uu____25381 = (matches_pat scrutinee1 p1)
in (match (uu____25381) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee1 rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
((FStar_TypeChecker_Cfg.log cfg1 (fun uu____25427 -> (

let uu____25428 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____25430 = (

let uu____25432 = (FStar_List.map (fun uu____25444 -> (match (uu____25444) with
| (uu____25450, t2) -> begin
(FStar_Syntax_Print.term_to_string t2)
end)) s)
in (FStar_All.pipe_right uu____25432 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" uu____25428 uu____25430)))));
(

let env0 = env1
in (

let env2 = (FStar_List.fold_left (fun env2 uu____25486 -> (match (uu____25486) with
| (bv, t2) -> begin
(

let uu____25509 = (

let uu____25516 = (

let uu____25519 = (FStar_Syntax_Syntax.mk_binder bv)
in FStar_Pervasives_Native.Some (uu____25519))
in (

let uu____25520 = (

let uu____25521 = (

let uu____25553 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ((([]), (t2)))))
in (([]), (t2), (uu____25553), (false)))
in Clos (uu____25521))
in ((uu____25516), (uu____25520))))
in (uu____25509)::env2)
end)) env1 s)
in (

let uu____25646 = (guard_when_clause wopt b rest)
in (norm cfg1 env2 stack1 uu____25646))));
)
end))
end))
in (match (cfg1.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.iota) with
| true -> begin
(matches scrutinee branches)
end
| uu____25648 -> begin
(norm_and_rebuild_match ())
end)))))))));
)
end))
end)));
))


let normalize_with_primitive_steps : FStar_TypeChecker_Cfg.primitive_step Prims.list  ->  FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun ps s e t -> (

let c = (FStar_TypeChecker_Cfg.config' ps s e)
in ((FStar_TypeChecker_Cfg.log_cfg c (fun uu____25679 -> (

let uu____25680 = (FStar_TypeChecker_Cfg.cfg_to_string c)
in (FStar_Util.print1 "Cfg = %s\n" uu____25680))));
(

let uu____25683 = (is_nbe_request s)
in (match (uu____25683) with
| true -> begin
((FStar_TypeChecker_Cfg.log_top c (fun uu____25689 -> (

let uu____25690 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Starting NBE for (%s) {\n" uu____25690))));
(FStar_TypeChecker_Cfg.log_top c (fun uu____25696 -> (

let uu____25697 = (FStar_TypeChecker_Cfg.cfg_to_string c)
in (FStar_Util.print1 ">>> cfg = %s\n" uu____25697))));
(

let uu____25700 = (FStar_Util.record_time (fun uu____25707 -> (nbe_eval c s t)))
in (match (uu____25700) with
| (r, ms) -> begin
((FStar_TypeChecker_Cfg.log_top c (fun uu____25716 -> (

let uu____25717 = (FStar_Syntax_Print.term_to_string r)
in (

let uu____25719 = (FStar_Util.string_of_int ms)
in (FStar_Util.print2 "}\nNormalization result = (%s) in %s ms\n" uu____25717 uu____25719)))));
r;
)
end));
)
end
| uu____25722 -> begin
((FStar_TypeChecker_Cfg.log_top c (fun uu____25727 -> (

let uu____25728 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Starting normalizer for (%s) {\n" uu____25728))));
(FStar_TypeChecker_Cfg.log_top c (fun uu____25734 -> (

let uu____25735 = (FStar_TypeChecker_Cfg.cfg_to_string c)
in (FStar_Util.print1 ">>> cfg = %s\n" uu____25735))));
(

let uu____25738 = (FStar_Util.record_time (fun uu____25745 -> (norm c [] [] t)))
in (match (uu____25738) with
| (r, ms) -> begin
((FStar_TypeChecker_Cfg.log_top c (fun uu____25760 -> (

let uu____25761 = (FStar_Syntax_Print.term_to_string r)
in (

let uu____25763 = (FStar_Util.string_of_int ms)
in (FStar_Util.print2 "}\nNormalization result = (%s) in %s ms\n" uu____25761 uu____25763)))));
r;
)
end));
)
end));
)))


let normalize : FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (normalize_with_primitive_steps [] s e t))


let normalize_comp : FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (

let uu____25798 = (FStar_TypeChecker_Cfg.config s e)
in (norm_comp uu____25798 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let uu____25816 = (FStar_TypeChecker_Cfg.config [] env)
in (norm_universe uu____25816 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (

let cfg = (FStar_TypeChecker_Cfg.config ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.Unascribe)::(FStar_TypeChecker_Env.ForExtraction)::[]) env)
in (

let non_info = (fun t -> (

let uu____25842 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____25842)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____25849) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let uu___3144_25868 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.pos = uu___3144_25868.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___3144_25868.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____25875 = ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ))
in (match (uu____25875) with
| true -> begin
(

let ct1 = (

let uu____25879 = (downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)
in (match (uu____25879) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let flags = (

let uu____25886 = (FStar_Ident.lid_equals pure_eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____25886) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::ct.FStar_Syntax_Syntax.flags
end
| uu____25891 -> begin
ct.FStar_Syntax_Syntax.flags
end))
in (

let uu___3154_25893 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___3154_25893.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = uu___3154_25893.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___3154_25893.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags}))
end
| FStar_Pervasives_Native.None -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev cfg.FStar_TypeChecker_Cfg.tcenv c)
in (

let uu___3158_25895 = ct1
in {FStar_Syntax_Syntax.comp_univs = uu___3158_25895.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu___3158_25895.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___3158_25895.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___3158_25895.FStar_Syntax_Syntax.flags}))
end))
in (

let uu___3161_25896 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___3161_25896.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___3161_25896.FStar_Syntax_Syntax.vars}))
end
| uu____25897 -> begin
c
end)))
end
| uu____25899 -> begin
c
end))))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (FStar_TypeChecker_Cfg.config ((FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.Unascribe)::(FStar_TypeChecker_Env.ForExtraction)::[]) env)
in (

let non_info = (fun t -> (

let uu____25919 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____25919)))
in (

let uu____25926 = ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ))
in (match (uu____25926) with
| true -> begin
(

let uu____25929 = (downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____25929) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(FStar_Syntax_Syntax.mk_lcomp pure_eff lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____25935 -> (

let uu____25936 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (ghost_to_pure env uu____25936))))
end
| FStar_Pervasives_Native.None -> begin
lc
end))
end
| uu____25937 -> begin
lc
end)))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (

let t1 = (FStar_All.try_with (fun uu___3177_25953 -> (match (()) with
| () -> begin
(normalize ((FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env t)
end)) (fun uu___3176_25956 -> ((

let uu____25958 = (

let uu____25964 = (

let uu____25966 = (FStar_Util.message_of_exn uu___3176_25956)
in (FStar_Util.format1 "Normalization failed with error %s\n" uu____25966))
in ((FStar_Errors.Warning_NormalizationFailure), (uu____25964)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____25958));
t;
)))
in (FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let c1 = (FStar_All.try_with (fun uu___3187_25985 -> (match (()) with
| () -> begin
(

let uu____25986 = (FStar_TypeChecker_Cfg.config ((FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env)
in (norm_comp uu____25986 [] c))
end)) (fun uu___3186_25995 -> ((

let uu____25997 = (

let uu____26003 = (

let uu____26005 = (FStar_Util.message_of_exn uu___3186_25995)
in (FStar_Util.format1 "Normalization failed with error %s\n" uu____26005))
in ((FStar_Errors.Warning_NormalizationFailure), (uu____26003)))
in (FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____25997));
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

let uu____26054 = (

let uu____26055 = (

let uu____26062 = (FStar_Syntax_Util.mk_conj_simp phi1 phi)
in ((y), (uu____26062)))
in FStar_Syntax_Syntax.Tm_refine (uu____26055))
in (mk uu____26054 t01.FStar_Syntax_Syntax.pos))
end
| uu____26067 -> begin
t2
end))
end
| uu____26068 -> begin
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
| uu____26120 -> begin
[]
end) ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.CompressUvars)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota))::(FStar_TypeChecker_Env.NoFullNorm)::[])) env t))


let reduce_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions false env t))


let remove_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions true env t))


let eta_expand_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e t_e -> (

let uu____26162 = (FStar_Syntax_Util.arrow_formals_comp t_e)
in (match (uu____26162) with
| (formals, c) -> begin
(match (formals) with
| [] -> begin
e
end
| uu____26199 -> begin
(

let uu____26208 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____26208) with
| (actuals, uu____26218, uu____26219) -> begin
(match ((Prims.op_Equality (FStar_List.length actuals) (FStar_List.length formals))) with
| true -> begin
e
end
| uu____26237 -> begin
(

let uu____26239 = (FStar_All.pipe_right formals FStar_Syntax_Util.args_of_binders)
in (match (uu____26239) with
| (binders, args) -> begin
(

let uu____26250 = (FStar_Syntax_Syntax.mk_Tm_app e args FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Util.abs binders uu____26250 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c)))))
end))
end)
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(eta_expand_with_type env t x.FStar_Syntax_Syntax.sort)
end
| uu____26265 -> begin
(

let uu____26266 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____26266) with
| (head1, args) -> begin
(

let uu____26309 = (

let uu____26310 = (FStar_Syntax_Subst.compress head1)
in uu____26310.FStar_Syntax_Syntax.n)
in (match (uu____26309) with
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____26331 = (

let uu____26346 = (FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Syntax_Util.arrow_formals uu____26346))
in (match (uu____26331) with
| (formals, _tres) -> begin
(match ((Prims.op_Equality (FStar_List.length formals) (FStar_List.length args))) with
| true -> begin
t
end
| uu____26384 -> begin
(

let uu____26386 = (env.FStar_TypeChecker_Env.type_of (

let uu___3257_26394 = env
in {FStar_TypeChecker_Env.solver = uu___3257_26394.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___3257_26394.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___3257_26394.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___3257_26394.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___3257_26394.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___3257_26394.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___3257_26394.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___3257_26394.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___3257_26394.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___3257_26394.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___3257_26394.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___3257_26394.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___3257_26394.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___3257_26394.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___3257_26394.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___3257_26394.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___3257_26394.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___3257_26394.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___3257_26394.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___3257_26394.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___3257_26394.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___3257_26394.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___3257_26394.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___3257_26394.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___3257_26394.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___3257_26394.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___3257_26394.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___3257_26394.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___3257_26394.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___3257_26394.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___3257_26394.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___3257_26394.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___3257_26394.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___3257_26394.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___3257_26394.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___3257_26394.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___3257_26394.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___3257_26394.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___3257_26394.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___3257_26394.FStar_TypeChecker_Env.nbe}) t)
in (match (uu____26386) with
| (uu____26397, ty, uu____26399) -> begin
(eta_expand_with_type env t ty)
end))
end)
end))
end
| uu____26400 -> begin
(

let uu____26401 = (env.FStar_TypeChecker_Env.type_of (

let uu___3264_26409 = env
in {FStar_TypeChecker_Env.solver = uu___3264_26409.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___3264_26409.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___3264_26409.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___3264_26409.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___3264_26409.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___3264_26409.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___3264_26409.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___3264_26409.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___3264_26409.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___3264_26409.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___3264_26409.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___3264_26409.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___3264_26409.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___3264_26409.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___3264_26409.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___3264_26409.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___3264_26409.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___3264_26409.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___3264_26409.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___3264_26409.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___3264_26409.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___3264_26409.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___3264_26409.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___3264_26409.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___3264_26409.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___3264_26409.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___3264_26409.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___3264_26409.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___3264_26409.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___3264_26409.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___3264_26409.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___3264_26409.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___3264_26409.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___3264_26409.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___3264_26409.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___3264_26409.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___3264_26409.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___3264_26409.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___3264_26409.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___3264_26409.FStar_TypeChecker_Env.nbe}) t)
in (match (uu____26401) with
| (uu____26412, ty, uu____26414) -> begin
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

let uu___3276_26496 = x
in (

let uu____26497 = (elim_delayed_subst_term x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___3276_26496.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___3276_26496.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____26497})))
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____26500) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_bvar (uu____26524) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_name (uu____26525) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_fvar (uu____26526) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uinst (uu____26527) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_constant (uu____26534) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (uu____26535) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_lazy (uu____26536) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t1
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, rc_opt) -> begin
(

let elim_rc = (fun rc -> (

let uu___3302_26570 = rc
in (

let uu____26571 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ elim_delayed_subst_term)
in (

let uu____26580 = (elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags)
in {FStar_Syntax_Syntax.residual_effect = uu___3302_26570.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____26571; FStar_Syntax_Syntax.residual_flags = uu____26580}))))
in (

let uu____26583 = (

let uu____26584 = (

let uu____26603 = (elim_delayed_subst_binders bs)
in (

let uu____26612 = (elim_delayed_subst_term t2)
in (

let uu____26615 = (FStar_Util.map_opt rc_opt elim_rc)
in ((uu____26603), (uu____26612), (uu____26615)))))
in FStar_Syntax_Syntax.Tm_abs (uu____26584))
in (mk1 uu____26583)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____26652 = (

let uu____26653 = (

let uu____26668 = (elim_delayed_subst_binders bs)
in (

let uu____26677 = (elim_delayed_subst_comp c)
in ((uu____26668), (uu____26677))))
in FStar_Syntax_Syntax.Tm_arrow (uu____26653))
in (mk1 uu____26652))
end
| FStar_Syntax_Syntax.Tm_refine (bv, phi) -> begin
(

let uu____26696 = (

let uu____26697 = (

let uu____26704 = (elim_bv bv)
in (

let uu____26705 = (elim_delayed_subst_term phi)
in ((uu____26704), (uu____26705))))
in FStar_Syntax_Syntax.Tm_refine (uu____26697))
in (mk1 uu____26696))
end
| FStar_Syntax_Syntax.Tm_app (t2, args) -> begin
(

let uu____26736 = (

let uu____26737 = (

let uu____26754 = (elim_delayed_subst_term t2)
in (

let uu____26757 = (elim_delayed_subst_args args)
in ((uu____26754), (uu____26757))))
in FStar_Syntax_Syntax.Tm_app (uu____26737))
in (mk1 uu____26736))
end
| FStar_Syntax_Syntax.Tm_match (t2, branches) -> begin
(

let rec elim_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu___3324_26829 = p
in (

let uu____26830 = (

let uu____26831 = (elim_bv x)
in FStar_Syntax_Syntax.Pat_var (uu____26831))
in {FStar_Syntax_Syntax.v = uu____26830; FStar_Syntax_Syntax.p = uu___3324_26829.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu___3328_26833 = p
in (

let uu____26834 = (

let uu____26835 = (elim_bv x)
in FStar_Syntax_Syntax.Pat_wild (uu____26835))
in {FStar_Syntax_Syntax.v = uu____26834; FStar_Syntax_Syntax.p = uu___3328_26833.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let uu___3334_26842 = p
in (

let uu____26843 = (

let uu____26844 = (

let uu____26851 = (elim_bv x)
in (

let uu____26852 = (elim_delayed_subst_term t0)
in ((uu____26851), (uu____26852))))
in FStar_Syntax_Syntax.Pat_dot_term (uu____26844))
in {FStar_Syntax_Syntax.v = uu____26843; FStar_Syntax_Syntax.p = uu___3334_26842.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu___3340_26877 = p
in (

let uu____26878 = (

let uu____26879 = (

let uu____26893 = (FStar_List.map (fun uu____26919 -> (match (uu____26919) with
| (x, b) -> begin
(

let uu____26936 = (elim_pat x)
in ((uu____26936), (b)))
end)) pats)
in ((fv), (uu____26893)))
in FStar_Syntax_Syntax.Pat_cons (uu____26879))
in {FStar_Syntax_Syntax.v = uu____26878; FStar_Syntax_Syntax.p = uu___3340_26877.FStar_Syntax_Syntax.p}))
end
| uu____26951 -> begin
p
end))
in (

let elim_branch = (fun uu____26975 -> (match (uu____26975) with
| (pat, wopt, t3) -> begin
(

let uu____27001 = (elim_pat pat)
in (

let uu____27004 = (FStar_Util.map_opt wopt elim_delayed_subst_term)
in (

let uu____27007 = (elim_delayed_subst_term t3)
in ((uu____27001), (uu____27004), (uu____27007)))))
end))
in (

let uu____27012 = (

let uu____27013 = (

let uu____27036 = (elim_delayed_subst_term t2)
in (

let uu____27039 = (FStar_List.map elim_branch branches)
in ((uu____27036), (uu____27039))))
in FStar_Syntax_Syntax.Tm_match (uu____27013))
in (mk1 uu____27012))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, a, lopt) -> begin
(

let elim_ascription = (fun uu____27170 -> (match (uu____27170) with
| (tc, topt) -> begin
(

let uu____27205 = (match (tc) with
| FStar_Util.Inl (t3) -> begin
(

let uu____27215 = (elim_delayed_subst_term t3)
in FStar_Util.Inl (uu____27215))
end
| FStar_Util.Inr (c) -> begin
(

let uu____27217 = (elim_delayed_subst_comp c)
in FStar_Util.Inr (uu____27217))
end)
in (

let uu____27218 = (FStar_Util.map_opt topt elim_delayed_subst_term)
in ((uu____27205), (uu____27218))))
end))
in (

let uu____27227 = (

let uu____27228 = (

let uu____27255 = (elim_delayed_subst_term t2)
in (

let uu____27258 = (elim_ascription a)
in ((uu____27255), (uu____27258), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____27228))
in (mk1 uu____27227)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t2) -> begin
(

let elim_lb = (fun lb -> (

let uu___3370_27321 = lb
in (

let uu____27322 = (elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____27325 = (elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___3370_27321.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___3370_27321.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____27322; FStar_Syntax_Syntax.lbeff = uu___3370_27321.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____27325; FStar_Syntax_Syntax.lbattrs = uu___3370_27321.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___3370_27321.FStar_Syntax_Syntax.lbpos}))))
in (

let uu____27328 = (

let uu____27329 = (

let uu____27343 = (

let uu____27351 = (FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs))
in (((FStar_Pervasives_Native.fst lbs)), (uu____27351)))
in (

let uu____27363 = (elim_delayed_subst_term t2)
in ((uu____27343), (uu____27363))))
in FStar_Syntax_Syntax.Tm_let (uu____27329))
in (mk1 uu____27328)))
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uvar (((u), (s)))))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi)
in (

let uu____27408 = (

let uu____27409 = (

let uu____27416 = (elim_delayed_subst_term tm)
in ((uu____27416), (qi1)))
in FStar_Syntax_Syntax.Tm_quoted (uu____27409))
in (mk1 uu____27408)))
end
| FStar_Syntax_Syntax.Tm_meta (t2, md) -> begin
(

let uu____27427 = (

let uu____27428 = (

let uu____27435 = (elim_delayed_subst_term t2)
in (

let uu____27438 = (elim_delayed_subst_meta md)
in ((uu____27435), (uu____27438))))
in FStar_Syntax_Syntax.Tm_meta (uu____27428))
in (mk1 uu____27427))
end)))))
and elim_delayed_subst_cflags : FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun flags -> (FStar_List.map (fun uu___18_27447 -> (match (uu___18_27447) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____27451 = (elim_delayed_subst_term t)
in FStar_Syntax_Syntax.DECREASES (uu____27451))
end
| f -> begin
f
end)) flags))
and elim_delayed_subst_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun c -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____27474 = (

let uu____27475 = (

let uu____27484 = (elim_delayed_subst_term t)
in ((uu____27484), (uopt)))
in FStar_Syntax_Syntax.Total (uu____27475))
in (mk1 uu____27474))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____27501 = (

let uu____27502 = (

let uu____27511 = (elim_delayed_subst_term t)
in ((uu____27511), (uopt)))
in FStar_Syntax_Syntax.GTotal (uu____27502))
in (mk1 uu____27501))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___3403_27520 = ct
in (

let uu____27521 = (elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____27524 = (elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args)
in (

let uu____27535 = (elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu___3403_27520.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___3403_27520.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____27521; FStar_Syntax_Syntax.effect_args = uu____27524; FStar_Syntax_Syntax.flags = uu____27535}))))
in (mk1 (FStar_Syntax_Syntax.Comp (ct1))))
end)))
and elim_delayed_subst_meta : FStar_Syntax_Syntax.metadata  ->  FStar_Syntax_Syntax.metadata = (fun uu___19_27538 -> (match (uu___19_27538) with
| FStar_Syntax_Syntax.Meta_pattern (names1, args) -> begin
(

let uu____27573 = (

let uu____27594 = (FStar_List.map elim_delayed_subst_term names1)
in (

let uu____27603 = (FStar_List.map elim_delayed_subst_args args)
in ((uu____27594), (uu____27603))))
in FStar_Syntax_Syntax.Meta_pattern (uu____27573))
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let uu____27658 = (

let uu____27665 = (elim_delayed_subst_term t)
in ((m), (uu____27665)))
in FStar_Syntax_Syntax.Meta_monadic (uu____27658))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t) -> begin
(

let uu____27677 = (

let uu____27686 = (elim_delayed_subst_term t)
in ((m1), (m2), (uu____27686)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____27677))
end
| m -> begin
m
end))
and elim_delayed_subst_args : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun args -> (FStar_List.map (fun uu____27719 -> (match (uu____27719) with
| (t, q) -> begin
(

let uu____27738 = (elim_delayed_subst_term t)
in ((uu____27738), (q)))
end)) args))
and elim_delayed_subst_binders : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun bs -> (FStar_List.map (fun uu____27766 -> (match (uu____27766) with
| (x, q) -> begin
(

let uu____27785 = (

let uu___3429_27786 = x
in (

let uu____27787 = (elim_delayed_subst_term x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___3429_27786.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___3429_27786.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____27787}))
in ((uu____27785), (q)))
end)) bs))


let elim_uvars_aux_tc : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.comp) FStar_Util.either  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either) = (fun env univ_names binders tc -> (

let t = (match (((binders), (tc))) with
| ([], FStar_Util.Inl (t)) -> begin
t
end
| ([], FStar_Util.Inr (c)) -> begin
(failwith "Impossible: empty bindes with a comp")
end
| (uu____27895, FStar_Util.Inr (c)) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
end
| (uu____27927, FStar_Util.Inl (t)) -> begin
(

let uu____27949 = (

let uu____27956 = (

let uu____27957 = (

let uu____27972 = (FStar_Syntax_Syntax.mk_Total t)
in ((binders), (uu____27972)))
in FStar_Syntax_Syntax.Tm_arrow (uu____27957))
in (FStar_Syntax_Syntax.mk uu____27956))
in (uu____27949 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end)
in (

let uu____27985 = (FStar_Syntax_Subst.open_univ_vars univ_names t)
in (match (uu____27985) with
| (univ_names1, t1) -> begin
(

let t2 = (remove_uvar_solutions env t1)
in (

let t3 = (FStar_Syntax_Subst.close_univ_vars univ_names1 t2)
in (

let t4 = (elim_delayed_subst_term t3)
in (

let uu____28017 = (match (binders) with
| [] -> begin
(([]), (FStar_Util.Inl (t4)))
end
| uu____28090 -> begin
(

let uu____28091 = (

let uu____28100 = (

let uu____28101 = (FStar_Syntax_Subst.compress t4)
in uu____28101.FStar_Syntax_Syntax.n)
in ((uu____28100), (tc)))
in (match (uu____28091) with
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inr (uu____28130)) -> begin
((binders1), (FStar_Util.Inr (c)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inl (uu____28177)) -> begin
((binders1), (FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))))
end
| (uu____28222, FStar_Util.Inl (uu____28223)) -> begin
(([]), (FStar_Util.Inl (t4)))
end
| uu____28254 -> begin
(failwith "Impossible")
end))
end)
in (match (uu____28017) with
| (binders1, tc1) -> begin
((univ_names1), (binders1), (tc1))
end)))))
end))))


let elim_uvars_aux_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun env univ_names binders t -> (

let uu____28393 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl (t)))
in (match (uu____28393) with
| (univ_names1, binders1, tc) -> begin
(

let uu____28467 = (FStar_Util.left tc)
in ((univ_names1), (binders1), (uu____28467)))
end)))


let elim_uvars_aux_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) = (fun env univ_names binders c -> (

let uu____28521 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr (c)))
in (match (uu____28521) with
| (univ_names1, binders1, tc) -> begin
(

let uu____28595 = (FStar_Util.right tc)
in ((univ_names1), (binders1), (uu____28595)))
end)))


let rec elim_uvars : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, lids, lids') -> begin
(

let uu____28637 = (elim_uvars_aux_t env univ_names binders typ)
in (match (uu____28637) with
| (univ_names1, binders1, typ1) -> begin
(

let uu___3512_28677 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univ_names1), (binders1), (typ1), (lids), (lids'))); FStar_Syntax_Syntax.sigrng = uu___3512_28677.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3512_28677.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3512_28677.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3512_28677.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uu___3518_28692 = s
in (

let uu____28693 = (

let uu____28694 = (

let uu____28703 = (FStar_List.map (elim_uvars env) sigs)
in ((uu____28703), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____28694))
in {FStar_Syntax_Syntax.sigel = uu____28693; FStar_Syntax_Syntax.sigrng = uu___3518_28692.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3518_28692.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3518_28692.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3518_28692.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univ_names, typ, lident, i, lids) -> begin
(

let uu____28722 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____28722) with
| (univ_names1, uu____28746, typ1) -> begin
(

let uu___3532_28768 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univ_names1), (typ1), (lident), (i), (lids))); FStar_Syntax_Syntax.sigrng = uu___3532_28768.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3532_28768.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3532_28768.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3532_28768.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) -> begin
(

let uu____28775 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____28775) with
| (univ_names1, uu____28799, typ1) -> begin
(

let uu___3543_28821 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (univ_names1), (typ1))); FStar_Syntax_Syntax.sigrng = uu___3543_28821.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3543_28821.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3543_28821.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3543_28821.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____28851 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____28851) with
| (opening, lbunivs) -> begin
(

let elim = (fun t -> (

let uu____28876 = (

let uu____28877 = (

let uu____28878 = (FStar_Syntax_Subst.subst opening t)
in (remove_uvar_solutions env uu____28878))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____28877))
in (elim_delayed_subst_term uu____28876)))
in (

let lbtyp = (elim lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (elim lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___3559_28881 = lb
in {FStar_Syntax_Syntax.lbname = uu___3559_28881.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___3559_28881.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___3559_28881.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___3559_28881.FStar_Syntax_Syntax.lbpos}))))
end)))))
in (

let uu___3562_28882 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((b), (lbs1))), (lids))); FStar_Syntax_Syntax.sigrng = uu___3562_28882.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3562_28882.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3562_28882.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3562_28882.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(

let uu___3566_28889 = s
in (

let uu____28890 = (

let uu____28891 = (remove_uvar_solutions env t)
in FStar_Syntax_Syntax.Sig_main (uu____28891))
in {FStar_Syntax_Syntax.sigel = uu____28890; FStar_Syntax_Syntax.sigrng = uu___3566_28889.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3566_28889.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3566_28889.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3566_28889.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, t) -> begin
(

let uu____28895 = (elim_uvars_aux_t env us [] t)
in (match (uu____28895) with
| (us1, uu____28919, t1) -> begin
(

let uu___3577_28941 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((l), (us1), (t1))); FStar_Syntax_Syntax.sigrng = uu___3577_28941.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3577_28941.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3577_28941.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3577_28941.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____28942) -> begin
(failwith "Impossible: should have been desugared already")
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____28945 = (elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____28945) with
| (univs1, binders, signature) -> begin
(

let uu____28985 = (

let uu____28990 = (FStar_Syntax_Subst.univ_var_opening univs1)
in (match (uu____28990) with
| (univs_opening, univs2) -> begin
(

let uu____29013 = (FStar_Syntax_Subst.univ_var_closing univs2)
in ((univs_opening), (uu____29013)))
end))
in (match (uu____28985) with
| (univs_opening, univs_closing) -> begin
(

let uu____29016 = (

let binders1 = (FStar_Syntax_Subst.open_binders binders)
in (

let uu____29022 = (FStar_Syntax_Subst.opening_of_binders binders1)
in (

let uu____29023 = (FStar_Syntax_Subst.closing_of_binders binders1)
in ((uu____29022), (uu____29023)))))
in (match (uu____29016) with
| (b_opening, b_closing) -> begin
(

let n1 = (FStar_List.length univs1)
in (

let n_binders = (FStar_List.length binders)
in (

let elim_tscheme = (fun uu____29049 -> (match (uu____29049) with
| (us, t) -> begin
(

let n_us = (FStar_List.length us)
in (

let uu____29067 = (FStar_Syntax_Subst.open_univ_vars us t)
in (match (uu____29067) with
| (us1, t1) -> begin
(

let uu____29078 = (

let uu____29087 = (FStar_All.pipe_right b_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____29092 = (FStar_All.pipe_right b_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____29087), (uu____29092))))
in (match (uu____29078) with
| (b_opening1, b_closing1) -> begin
(

let uu____29115 = (

let uu____29124 = (FStar_All.pipe_right univs_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____29129 = (FStar_All.pipe_right univs_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____29124), (uu____29129))))
in (match (uu____29115) with
| (univs_opening1, univs_closing1) -> begin
(

let t2 = (

let uu____29153 = (FStar_Syntax_Subst.subst b_opening1 t1)
in (FStar_Syntax_Subst.subst univs_opening1 uu____29153))
in (

let uu____29154 = (elim_uvars_aux_t env [] [] t2)
in (match (uu____29154) with
| (uu____29181, uu____29182, t3) -> begin
(

let t4 = (

let uu____29205 = (

let uu____29206 = (FStar_Syntax_Subst.close_univ_vars us1 t3)
in (FStar_Syntax_Subst.subst b_closing1 uu____29206))
in (FStar_Syntax_Subst.subst univs_closing1 uu____29205))
in ((us1), (t4)))
end)))
end))
end))
end)))
end))
in (

let elim_term = (fun t -> (

let uu____29215 = (elim_uvars_aux_t env univs1 binders t)
in (match (uu____29215) with
| (uu____29234, uu____29235, t1) -> begin
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
| uu____29311 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((a.FStar_Syntax_Syntax.action_params), (body), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
end))
in (

let destruct_action_body = (fun body -> (

let uu____29338 = (

let uu____29339 = (FStar_Syntax_Subst.compress body)
in uu____29339.FStar_Syntax_Syntax.n)
in (match (uu____29338) with
| FStar_Syntax_Syntax.Tm_ascribed (defn, (FStar_Util.Inl (typ), FStar_Pervasives_Native.None), FStar_Pervasives_Native.None) -> begin
((defn), (typ))
end
| uu____29398 -> begin
(failwith "Impossible")
end)))
in (

let destruct_action_typ_templ = (fun t -> (

let uu____29432 = (

let uu____29433 = (FStar_Syntax_Subst.compress t)
in uu____29433.FStar_Syntax_Syntax.n)
in (match (uu____29432) with
| FStar_Syntax_Syntax.Tm_abs (pars, body, uu____29456) -> begin
(

let uu____29481 = (destruct_action_body body)
in (match (uu____29481) with
| (defn, typ) -> begin
((pars), (defn), (typ))
end))
end
| uu____29530 -> begin
(

let uu____29531 = (destruct_action_body t)
in (match (uu____29531) with
| (defn, typ) -> begin
(([]), (defn), (typ))
end))
end)))
in (

let uu____29586 = (elim_tscheme ((a.FStar_Syntax_Syntax.action_univs), (action_typ_templ)))
in (match (uu____29586) with
| (action_univs, t) -> begin
(

let uu____29595 = (destruct_action_typ_templ t)
in (match (uu____29595) with
| (action_params, action_defn, action_typ) -> begin
(

let a' = (

let uu___3663_29642 = a
in {FStar_Syntax_Syntax.action_name = uu___3663_29642.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___3663_29642.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action_univs; FStar_Syntax_Syntax.action_params = action_params; FStar_Syntax_Syntax.action_defn = action_defn; FStar_Syntax_Syntax.action_typ = action_typ})
in a')
end))
end))))))
in (

let ed1 = (

let uu___3666_29644 = ed
in (

let uu____29645 = (elim_tscheme ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____29646 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____29647 = (elim_tscheme ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____29648 = (elim_tscheme ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____29649 = (elim_tscheme ed.FStar_Syntax_Syntax.stronger)
in (

let uu____29650 = (elim_tscheme ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____29651 = (elim_tscheme ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____29652 = (elim_tscheme ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____29653 = (elim_tscheme ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____29654 = (elim_tscheme ed.FStar_Syntax_Syntax.trivial)
in (

let uu____29655 = (elim_term ed.FStar_Syntax_Syntax.repr)
in (

let uu____29656 = (elim_tscheme ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____29657 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____29658 = (FStar_List.map elim_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___3666_29644.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___3666_29644.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu____29645; FStar_Syntax_Syntax.bind_wp = uu____29646; FStar_Syntax_Syntax.if_then_else = uu____29647; FStar_Syntax_Syntax.ite_wp = uu____29648; FStar_Syntax_Syntax.stronger = uu____29649; FStar_Syntax_Syntax.close_wp = uu____29650; FStar_Syntax_Syntax.assert_p = uu____29651; FStar_Syntax_Syntax.assume_p = uu____29652; FStar_Syntax_Syntax.null_wp = uu____29653; FStar_Syntax_Syntax.trivial = uu____29654; FStar_Syntax_Syntax.repr = uu____29655; FStar_Syntax_Syntax.return_repr = uu____29656; FStar_Syntax_Syntax.bind_repr = uu____29657; FStar_Syntax_Syntax.actions = uu____29658; FStar_Syntax_Syntax.eff_attrs = uu___3666_29644.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in (

let uu___3669_29661 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ed1); FStar_Syntax_Syntax.sigrng = uu___3669_29661.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3669_29661.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3669_29661.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3669_29661.FStar_Syntax_Syntax.sigattrs})))))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub_eff) -> begin
(

let elim_tscheme_opt = (fun uu___20_29682 -> (match (uu___20_29682) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (us, t) -> begin
(

let uu____29713 = (elim_uvars_aux_t env us [] t)
in (match (uu____29713) with
| (us1, uu____29745, t1) -> begin
FStar_Pervasives_Native.Some (((us1), (t1)))
end))
end))
in (

let sub_eff1 = (

let uu___3684_29776 = sub_eff
in (

let uu____29777 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp)
in (

let uu____29780 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift)
in {FStar_Syntax_Syntax.source = uu___3684_29776.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___3684_29776.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = uu____29777; FStar_Syntax_Syntax.lift = uu____29780})))
in (

let uu___3687_29783 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub_eff1); FStar_Syntax_Syntax.sigrng = uu___3687_29783.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3687_29783.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3687_29783.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3687_29783.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univ_names, binders, comp, flags) -> begin
(

let uu____29793 = (elim_uvars_aux_c env univ_names binders comp)
in (match (uu____29793) with
| (univ_names1, binders1, comp1) -> begin
(

let uu___3700_29833 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (univ_names1), (binders1), (comp1), (flags))); FStar_Syntax_Syntax.sigrng = uu___3700_29833.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3700_29833.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3700_29833.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3700_29833.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_pragma (uu____29836) -> begin
s
end
| FStar_Syntax_Syntax.Sig_splice (uu____29837) -> begin
s
end))


let erase_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env t))


let unfold_head_once : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env t -> (

let aux = (fun f us args -> (

let uu____29886 = (FStar_TypeChecker_Env.lookup_nonrec_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]) env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____29886) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (head_def_ts) -> begin
(

let uu____29908 = (FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us)
in (match (uu____29908) with
| (uu____29915, head_def) -> begin
(

let t' = (FStar_Syntax_Syntax.mk_Tm_app head_def args FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let t'1 = (normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::[]) env t')
in FStar_Pervasives_Native.Some (t'1)))
end))
end)))
in (

let uu____29921 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____29921) with
| (head1, args) -> begin
(

let uu____29966 = (

let uu____29967 = (FStar_Syntax_Subst.compress head1)
in uu____29967.FStar_Syntax_Syntax.n)
in (match (uu____29966) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(aux fv [] args)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____29974; FStar_Syntax_Syntax.vars = uu____29975}, us) -> begin
(aux fv us args)
end
| uu____29981 -> begin
FStar_Pervasives_Native.None
end))
end))))




