
open Prims
open FStar_Pervasives

let subst_to_string : 'Auu____5 . (FStar_Syntax_Syntax.bv * 'Auu____5) Prims.list  ->  Prims.string = (fun s -> (

let uu____22 = (FStar_All.pipe_right s (FStar_List.map (fun uu____40 -> (match (uu____40) with
| (b, uu____46) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right uu____22 (FStar_String.concat ", "))))


let rec apply_until_some : 'Auu____57 'Auu____58 . ('Auu____58  ->  'Auu____57 FStar_Pervasives_Native.option)  ->  'Auu____58 Prims.list  ->  ('Auu____58 Prims.list * 'Auu____57) FStar_Pervasives_Native.option = (fun f s -> (match (s) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (s0)::rest -> begin
(

let uu____98 = (f s0)
in (match (uu____98) with
| FStar_Pervasives_Native.None -> begin
(apply_until_some f rest)
end
| FStar_Pervasives_Native.Some (st) -> begin
FStar_Pervasives_Native.Some (((rest), (st)))
end))
end))


let map_some_curry : 'Auu____130 'Auu____131 'Auu____132 . ('Auu____132  ->  'Auu____131  ->  'Auu____130)  ->  'Auu____130  ->  ('Auu____132 * 'Auu____131) FStar_Pervasives_Native.option  ->  'Auu____130 = (fun f x uu___103_156 -> (match (uu___103_156) with
| FStar_Pervasives_Native.None -> begin
x
end
| FStar_Pervasives_Native.Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map : 'Auu____191 'Auu____192 'Auu____193 . ('Auu____193  ->  'Auu____192 FStar_Pervasives_Native.option)  ->  'Auu____193 Prims.list  ->  ('Auu____193 Prims.list  ->  'Auu____192  ->  'Auu____191)  ->  'Auu____191  ->  'Auu____191 = (fun f s g t -> (

let uu____237 = (apply_until_some f s)
in (FStar_All.pipe_right uu____237 (map_some_curry g t))))


let compose_subst : 'Auu____264 'Auu____265 . ('Auu____265 Prims.list * 'Auu____264 FStar_Pervasives_Native.option)  ->  ('Auu____265 Prims.list * 'Auu____264 FStar_Pervasives_Native.option)  ->  ('Auu____265 Prims.list * 'Auu____264 FStar_Pervasives_Native.option) = (fun s1 s2 -> (

let s = (FStar_List.append (FStar_Pervasives_Native.fst s1) (FStar_Pervasives_Native.fst s2))
in (

let ropt = (match ((FStar_Pervasives_Native.snd s2)) with
| FStar_Pervasives_Native.Some (uu____334) -> begin
(FStar_Pervasives_Native.snd s2)
end
| uu____339 -> begin
(FStar_Pervasives_Native.snd s1)
end)
in ((s), (ropt)))))


let delay : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term = (fun t s -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t'), ((compose_subst s' s))) t.FStar_Syntax_Syntax.pos)
end
| uu____447 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t), (s)) t.FStar_Syntax_Syntax.pos)
end))


let rec force_uvar' : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____473) -> begin
(

let uu____498 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____498) with
| FStar_Pervasives_Native.Some (t') -> begin
(force_uvar' t')
end
| uu____504 -> begin
t
end))
end
| uu____507 -> begin
t
end))


let force_uvar : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let t' = (force_uvar' t)
in (

let uu____521 = (FStar_Util.physical_equality t t')
in (match (uu____521) with
| true -> begin
t
end
| uu____526 -> begin
(delay t' (([]), (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))))
end))))


let rec force_delayed_thunk : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(

let uu____589 = (FStar_ST.op_Bang m)
in (match (uu____589) with
| FStar_Pervasives_Native.None -> begin
t
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let t'1 = (force_delayed_thunk t')
in ((FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some (t'1)));
t'1;
))
end))
end
| uu____745 -> begin
t
end))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(

let uu____759 = (FStar_Syntax_Unionfind.univ_find u')
in (match (uu____759) with
| FStar_Pervasives_Native.Some (u1) -> begin
(compress_univ u1)
end
| uu____763 -> begin
u
end))
end
| uu____766 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___104_785 -> (match (uu___104_785) with
| FStar_Syntax_Syntax.DB (i, x) when (Prims.op_Equality i a.FStar_Syntax_Syntax.index) -> begin
(

let uu____790 = (

let uu____791 = (

let uu____792 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x uu____792))
in (FStar_Syntax_Syntax.bv_to_name uu____791))
in FStar_Pervasives_Native.Some (uu____790))
end
| uu____793 -> begin
FStar_Pervasives_Native.None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___105_812 -> (match (uu___105_812) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____817 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___109_820 = a
in {FStar_Syntax_Syntax.ppname = uu___109_820.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___109_820.FStar_Syntax_Syntax.sort}))
in FStar_Pervasives_Native.Some (uu____817))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____829 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___106_847 -> (match (uu___106_847) with
| FStar_Syntax_Syntax.UN (y, t) when (Prims.op_Equality x y) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____852 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___107_870 -> (match (uu___107_870) with
| FStar_Syntax_Syntax.UD (y, i) when (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____875 -> begin
FStar_Pervasives_Native.None
end))))


let rec subst_univ : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun s u -> (

let u1 = (compress_univ u)
in (match (u1) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(apply_until_some_then_map (subst_univ_bv x) s subst_univ u1)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(apply_until_some_then_map (subst_univ_nm x) s subst_univ u1)
end
| FStar_Syntax_Syntax.U_zero -> begin
u1
end
| FStar_Syntax_Syntax.U_unknown -> begin
u1
end
| FStar_Syntax_Syntax.U_unif (uu____899) -> begin
u1
end
| FStar_Syntax_Syntax.U_succ (u2) -> begin
(

let uu____909 = (subst_univ s u2)
in FStar_Syntax_Syntax.U_succ (uu____909))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____913 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (uu____913))
end)))


let tag_with_range : 'Auu____922 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ('Auu____922 * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
t
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let r1 = (FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r)
in (

let t' = (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____955 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_bvar (uu____955))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____957 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_name (uu____957))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v1 = (

let uu___110_963 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1); FStar_Syntax_Syntax.p = uu___110_963.FStar_Syntax_Syntax.p})
in (

let fv1 = (

let uu___111_965 = fv
in {FStar_Syntax_Syntax.fv_name = v1; FStar_Syntax_Syntax.fv_delta = uu___111_965.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___111_965.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv1))))
end
| t' -> begin
t'
end)
in (

let uu___112_967 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___112_967.FStar_Syntax_Syntax.vars})))
end))


let tag_lid_with_range : 'Auu____976 . FStar_Ident.lident  ->  ('Auu____976 * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Ident.lident = (fun l s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____1000 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r)
in (FStar_Ident.set_lid_range l uu____1000))
end))


let mk_range : FStar_Range.range  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Range.range = (fun r s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
r
end
| FStar_Pervasives_Native.Some (r') -> begin
(FStar_Range.set_use_range r r')
end))


let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun s t -> (

let subst_tail = (fun tl1 -> (subst' ((tl1), ((FStar_Pervasives_Native.snd s)))))
in (match (s) with
| ([], FStar_Pervasives_Native.None) -> begin
t
end
| (([])::[], FStar_Pervasives_Native.None) -> begin
t
end
| uu____1118 -> begin
(

let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1128) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1133) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1138) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_delayed ((t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t'), ((compose_subst s' s))) t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) (FStar_Pervasives_Native.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) (FStar_Pervasives_Native.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____1247 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (

let uu____1248 = (

let uu____1251 = (

let uu____1252 = (subst_univ (FStar_Pervasives_Native.fst s) u)
in FStar_Syntax_Syntax.Tm_type (uu____1252))
in (FStar_Syntax_Syntax.mk uu____1251))
in (uu____1248 FStar_Pervasives_Native.None uu____1247)))
end
| uu____1262 -> begin
(

let uu____1263 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed ((t0), (s)) uu____1263))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___108_1277 -> (match (uu___108_1277) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(

let uu____1281 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (uu____1281))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| ([], FStar_Pervasives_Native.None) -> begin
t
end
| (([])::[], FStar_Pervasives_Native.None) -> begin
t
end
| uu____1315 -> begin
(

let uu___113_1326 = t
in (

let uu____1327 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____1334 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____1339 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____1342 = (FStar_List.map (fun uu____1367 -> (match (uu____1367) with
| (t1, imp) -> begin
(

let uu____1386 = (subst' s t1)
in ((uu____1386), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (

let uu____1391 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu____1327; FStar_Syntax_Syntax.effect_name = uu____1334; FStar_Syntax_Syntax.result_typ = uu____1339; FStar_Syntax_Syntax.effect_args = uu____1342; FStar_Syntax_Syntax.flags = uu____1391}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([], FStar_Pervasives_Native.None) -> begin
t
end
| (([])::[], FStar_Pervasives_Native.None) -> begin
t
end
| uu____1428 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uopt) -> begin
(

let uu____1451 = (subst' s t1)
in (

let uu____1452 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____1451 uu____1452)))
end
| FStar_Syntax_Syntax.GTotal (t1, uopt) -> begin
(

let uu____1471 = (subst' s t1)
in (

let uu____1472 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1471 uu____1472)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1482 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp uu____1482))
end)
end))


let shift : Prims.int  ->  FStar_Syntax_Syntax.subst_elt  ->  FStar_Syntax_Syntax.subst_elt = (fun n1 s -> (match (s) with
| FStar_Syntax_Syntax.DB (i, t) -> begin
FStar_Syntax_Syntax.DB ((((i + n1)), (t)))
end
| FStar_Syntax_Syntax.UN (i, t) -> begin
FStar_Syntax_Syntax.UN ((((i + n1)), (t)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
FStar_Syntax_Syntax.NM (((x), ((i + n1))))
end
| FStar_Syntax_Syntax.UD (x, i) -> begin
FStar_Syntax_Syntax.UD (((x), ((i + n1))))
end
| FStar_Syntax_Syntax.NT (uu____1499) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n1 s -> (FStar_List.map (shift n1) s))


let shift_subst' : 'Auu____1520 . Prims.int  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1520)  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1520) = (fun n1 s -> (

let uu____1547 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (shift_subst n1)))
in ((uu____1547), ((FStar_Pervasives_Native.snd s)))))


let subst_binder' : 'Auu____1566 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.bv * 'Auu____1566)  ->  (FStar_Syntax_Syntax.bv * 'Auu____1566) = (fun s uu____1582 -> (match (uu____1582) with
| (x, imp) -> begin
(

let uu____1589 = (

let uu___114_1590 = x
in (

let uu____1591 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___114_1590.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___114_1590.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1591}))
in ((uu____1589), (imp)))
end))


let subst_binders' : 'Auu____1600 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.bv * 'Auu____1600) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____1600) Prims.list = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1659 -> begin
(

let uu____1660 = (shift_subst' i s)
in (subst_binder' uu____1660 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (FStar_Pervasives_Native.None)) bs))


let subst_arg' : 'Auu____1691 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1691)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1691) = (fun s uu____1711 -> (match (uu____1711) with
| (t, imp) -> begin
(

let uu____1724 = (subst' s t)
in ((uu____1724), (imp)))
end))


let subst_args' : 'Auu____1734 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1734) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1734) Prims.list = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____1824) -> begin
((p1), (n1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1845 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1899 uu____1900 -> (match (((uu____1899), (uu____1900))) with
| ((pats1, n2), (p2, imp)) -> begin
(

let uu____1979 = (aux n2 p2)
in (match (uu____1979) with
| (p3, m) -> begin
(((((p3), (imp)))::pats1), (m))
end))
end)) (([]), (n1))))
in (match (uu____1845) with
| (pats1, n2) -> begin
(((

let uu___115_2037 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___115_2037.FStar_Syntax_Syntax.p})), (n2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___116_2063 = x
in (

let uu____2064 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___116_2063.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___116_2063.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2064}))
in (((

let uu___117_2070 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___117_2070.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___118_2086 = x
in (

let uu____2087 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___118_2086.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_2086.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2087}))
in (((

let uu___119_2093 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___119_2093.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___120_2114 = x
in (

let uu____2115 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___120_2114.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___120_2114.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2115}))
in (

let t01 = (subst' s1 t0)
in (((

let uu___121_2124 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___121_2124.FStar_Syntax_Syntax.p})), (n1)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s lopt -> (match (lopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____2146 = (

let uu___122_2147 = rc
in (

let uu____2148 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (subst' s))
in {FStar_Syntax_Syntax.residual_effect = uu___122_2147.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____2148; FStar_Syntax_Syntax.residual_flags = uu___122_2147.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____2146))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk1 = (fun t' -> (

let uu____2177 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2177)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2180) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_constant (uu____2207) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2212) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2221) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_type (uu____2242) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2243) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_name (uu____2244) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us1 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us)
in (

let uu____2260 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us1)
in (tag_with_range uu____2260 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(

let uu____2289 = (

let uu____2290 = (

let uu____2305 = (subst' s t0)
in (

let uu____2308 = (subst_args' s args)
in ((uu____2305), (uu____2308))))
in FStar_Syntax_Syntax.Tm_app (uu____2290))
in (mk1 uu____2289))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t1) -> begin
(

let uu____2403 = (subst' s t1)
in FStar_Util.Inl (uu____2403))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2417 = (subst_comp' s c)
in FStar_Util.Inr (uu____2417))
end)
in (

let uu____2424 = (

let uu____2425 = (

let uu____2452 = (subst' s t0)
in (

let uu____2455 = (

let uu____2472 = (FStar_Util.map_opt topt (subst' s))
in ((annot1), (uu____2472)))
in ((uu____2452), (uu____2455), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2425))
in (mk1 uu____2424)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n1 = (FStar_List.length bs)
in (

let s' = (shift_subst' n1 s)
in (

let uu____2556 = (

let uu____2557 = (

let uu____2574 = (subst_binders' s bs)
in (

let uu____2581 = (subst' s' body)
in (

let uu____2584 = (push_subst_lcomp s' lopt)
in ((uu____2574), (uu____2581), (uu____2584)))))
in FStar_Syntax_Syntax.Tm_abs (uu____2557))
in (mk1 uu____2556))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n1 = (FStar_List.length bs)
in (

let uu____2620 = (

let uu____2621 = (

let uu____2634 = (subst_binders' s bs)
in (

let uu____2641 = (

let uu____2644 = (shift_subst' n1 s)
in (subst_comp' uu____2644 comp))
in ((uu____2634), (uu____2641))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2621))
in (mk1 uu____2620)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x1 = (

let uu___123_2676 = x
in (

let uu____2677 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___123_2676.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_2676.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2677}))
in (

let phi1 = (

let uu____2683 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____2683 phi))
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((x1), (phi1)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t01 = (subst' s t0)
in (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____2810 -> (match (uu____2810) with
| (pat, wopt, branch) -> begin
(

let uu____2856 = (subst_pat' s pat)
in (match (uu____2856) with
| (pat1, n1) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____2904 = (subst' s1 w)
in FStar_Pervasives_Native.Some (uu____2904))
end)
in (

let branch1 = (subst' s1 branch)
in ((pat1), (wopt1), (branch1)))))
end))
end))))
in (mk1 (FStar_Syntax_Syntax.Tm_match (((t01), (pats1)))))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body) -> begin
(

let n1 = (FStar_List.length lbs)
in (

let sn = (shift_subst' n1 s)
in (

let body1 = (subst' sn body)
in (

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let lbt = (subst' s lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbd = (

let uu____2989 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____2989) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____2992 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___124_3004 = x
in {FStar_Syntax_Syntax.ppname = uu___124_3004.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___124_3004.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr (fv)
end)
in (

let uu___125_3006 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___125_3006.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___125_3006.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (mk1 (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs1))), (body1)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let uu____3033 = (

let uu____3034 = (

let uu____3041 = (subst' s t0)
in (

let uu____3044 = (

let uu____3045 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____3045))
in ((uu____3041), (uu____3044))))
in FStar_Syntax_Syntax.Tm_meta (uu____3034))
in (mk1 uu____3033))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) -> begin
(

let uu____3105 = (

let uu____3106 = (

let uu____3113 = (subst' s t0)
in (

let uu____3116 = (

let uu____3117 = (

let uu____3124 = (subst' s t1)
in ((m), (uu____3124)))
in FStar_Syntax_Syntax.Meta_monadic (uu____3117))
in ((uu____3113), (uu____3116))))
in FStar_Syntax_Syntax.Tm_meta (uu____3106))
in (mk1 uu____3105))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) -> begin
(

let uu____3143 = (

let uu____3144 = (

let uu____3151 = (subst' s t0)
in (

let uu____3154 = (

let uu____3155 = (

let uu____3164 = (subst' s t1)
in ((m1), (m2), (uu____3164)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____3155))
in ((uu____3151), (uu____3154))))
in FStar_Syntax_Syntax.Tm_meta (uu____3144))
in (mk1 uu____3143))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____3177 = (

let uu____3178 = (

let uu____3185 = (subst' s t1)
in ((uu____3185), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____3178))
in (mk1 uu____3177))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (force_delayed_thunk t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t2, s), memo) -> begin
(

let t' = (

let uu____3249 = (push_subst s t2)
in (compress uu____3249))
in ((FStar_Syntax_Unionfind.update_in_tx memo (FStar_Pervasives_Native.Some (t')));
t';
))
end
| uu____3269 -> begin
(

let t' = (force_uvar t1)
in (match (t'.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____3273) -> begin
(compress t')
end
| uu____3298 -> begin
t'
end))
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (subst' (([]), (FStar_Pervasives_Native.Some ((

let uu___126_3338 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = uu___126_3338.FStar_Range.use_range})))) t))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let closing_subst : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun bs -> (

let uu____3367 = (FStar_List.fold_right (fun uu____3390 uu____3391 -> (match (((uu____3390), (uu____3391))) with
| ((x, uu____3419), (subst1, n1)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n1))))::subst1), ((n1 + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____3367 FStar_Pervasives_Native.fst)))


let open_binders' : 'Auu____3454 . (FStar_Syntax_Syntax.bv * 'Auu____3454) Prims.list  ->  ((FStar_Syntax_Syntax.bv * 'Auu____3454) Prims.list * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun bs -> (

let rec aux = (fun bs1 o -> (match (bs1) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___127_3560 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____3561 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___127_3560.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___127_3560.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3561}))
in (

let o1 = (

let uu____3567 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____3567)
in (

let uu____3570 = (aux bs' o1)
in (match (uu____3570) with
| (bs'1, o2) -> begin
(((((x'), (imp)))::bs'1), (o2))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____3629 = (open_binders' bs)
in (FStar_Pervasives_Native.fst uu____3629)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____3664 = (open_binders' bs)
in (match (uu____3664) with
| (bs', opening) -> begin
(

let uu____3701 = (subst opening t)
in ((bs'), (uu____3701), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____3722 = (open_term' bs t)
in (match (uu____3722) with
| (b, t1, uu____3735) -> begin
((b), (t1))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____3748 = (open_binders' bs)
in (match (uu____3748) with
| (bs', opening) -> begin
(

let uu____3783 = (subst_comp opening t)
in ((bs'), (uu____3783)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec open_pat_aux = (fun sub1 renaming p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____3864) -> begin
((p1), (sub1), (renaming))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3893 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____3985 uu____3986 -> (match (((uu____3985), (uu____3986))) with
| ((pats1, sub2, renaming1), (p2, imp)) -> begin
(

let uu____4134 = (open_pat_aux sub2 renaming1 p2)
in (match (uu____4134) with
| (p3, sub3, renaming2) -> begin
(((((p3), (imp)))::pats1), (sub3), (renaming2))
end))
end)) (([]), (sub1), (renaming))))
in (match (uu____3893) with
| (pats1, sub2, renaming1) -> begin
(((

let uu___128_4304 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___128_4304.FStar_Syntax_Syntax.p})), (sub2), (renaming1))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___129_4323 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4324 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___129_4323.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___129_4323.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4324}))
in (

let sub2 = (

let uu____4330 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4330)
in (((

let uu___130_4344 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.p = uu___130_4344.FStar_Syntax_Syntax.p})), (sub2), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___131_4353 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4354 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___131_4353.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_4353.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4354}))
in (

let sub2 = (

let uu____4360 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4360)
in (((

let uu___132_4374 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.p = uu___132_4374.FStar_Syntax_Syntax.p})), (sub2), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___133_4388 = x
in (

let uu____4389 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___133_4388.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_4388.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4389}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___134_4404 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___134_4404.FStar_Syntax_Syntax.p})), (sub1), (renaming))))
end))
in (

let uu____4407 = (open_pat_aux [] [] p)
in (match (uu____4407) with
| (p1, sub1, uu____4434) -> begin
((p1), (sub1))
end))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____4462 -> (match (uu____4462) with
| (p, wopt, e) -> begin
(

let uu____4482 = (open_pat p)
in (match (uu____4482) with
| (p1, opening) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____4501 = (subst opening w)
in FStar_Pervasives_Native.Some (uu____4501))
end)
in (

let e1 = (subst opening e)
in ((p1), (wopt1), (e1))))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____4513 = (closing_subst bs)
in (subst uu____4513 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____4524 = (closing_subst bs)
in (subst_comp uu____4524 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs1 -> (match (bs1) with
| [] -> begin
[]
end
| ((x, imp))::tl1 -> begin
(

let x1 = (

let uu___135_4576 = x
in (

let uu____4577 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___135_4576.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___135_4576.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4577}))
in (

let s' = (

let uu____4583 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____4583)
in (

let uu____4586 = (aux s' tl1)
in (((x1), (imp)))::uu____4586)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let uu___136_4608 = lc
in (

let uu____4609 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___136_4608.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____4609; FStar_Syntax_Syntax.cflags = uu___136_4608.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____4614 -> (

let uu____4615 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s uu____4615)))}))))


let close_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4663) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4686 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4752 uu____4753 -> (match (((uu____4752), (uu____4753))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____4856 = (aux sub2 p2)
in (match (uu____4856) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4686) with
| (pats1, sub2) -> begin
(((

let uu___137_4958 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___137_4958.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___138_4977 = x
in (

let uu____4978 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___138_4977.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___138_4977.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4978}))
in (

let sub2 = (

let uu____4984 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____4984)
in (((

let uu___139_4992 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___139_4992.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___140_4997 = x
in (

let uu____4998 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___140_4997.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___140_4997.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4998}))
in (

let sub2 = (

let uu____5004 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5004)
in (((

let uu___141_5012 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___141_5012.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___142_5022 = x
in (

let uu____5023 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___142_5022.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___142_5022.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5023}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___143_5032 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___143_5032.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____5038 -> (match (uu____5038) with
| (p, wopt, e) -> begin
(

let uu____5058 = (close_pat p)
in (match (uu____5058) with
| (p1, closing) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____5089 = (subst closing w)
in FStar_Pervasives_Native.Some (uu____5089))
end)
in (

let e1 = (subst closing e)
in ((p1), (wopt1), (e1))))
end))
end))


let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n1 - i)), (FStar_Syntax_Syntax.U_name (u)))))))
in ((s), (us)))))


let univ_var_closing : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun us -> (

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD (((u), ((n1 - i)))))))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (

let uu____5148 = (univ_var_opening us)
in (match (uu____5148) with
| (s, us') -> begin
(

let t1 = (subst s t)
in ((us'), (t1)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____5190 = (univ_var_opening us)
in (match (uu____5190) with
| (s, us') -> begin
(

let uu____5213 = (subst_comp s c)
in ((us'), (uu____5213)))
end)))


let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun us t -> (

let s = (univ_var_closing us)
in (subst s t)))


let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun us c -> (

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD (((u), ((n1 - i)))))))
in (subst_comp s c))))


let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____5263 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5263) with
| true -> begin
((lbs), (t))
end
| uu____5272 -> begin
(

let uu____5273 = (FStar_List.fold_right (fun lb uu____5301 -> (match (uu____5301) with
| (i, lbs1, out) -> begin
(

let x = (

let uu____5334 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____5334))
in (((i + (Prims.parse_int "1"))), (((

let uu___144_5340 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___144_5340.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___144_5340.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___144_5340.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___144_5340.FStar_Syntax_Syntax.lbdef}))::lbs1), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
in (match (uu____5273) with
| (n_let_recs, lbs1, let_rec_opening) -> begin
(

let lbs2 = (FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let uu____5377 = (FStar_List.fold_right (fun u uu____5404 -> (match (uu____5404) with
| (i, us, out) -> begin
(((i + (Prims.parse_int "1"))), ((u)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u)))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____5377) with
| (uu____5444, us, u_let_rec_opening) -> begin
(

let uu___145_5455 = lb
in (

let uu____5456 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___145_5455.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu___145_5455.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___145_5455.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5456}))
end)))))
in (

let t1 = (subst let_rec_opening t)
in ((lbs2), (t1))))
end))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____5480 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5480) with
| true -> begin
((lbs), (t))
end
| uu____5489 -> begin
(

let uu____5490 = (FStar_List.fold_right (fun lb uu____5509 -> (match (uu____5509) with
| (i, out) -> begin
(

let uu____5528 = (

let uu____5531 = (

let uu____5532 = (

let uu____5537 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____5537), (i)))
in FStar_Syntax_Syntax.NM (uu____5532))
in (uu____5531)::out)
in (((i + (Prims.parse_int "1"))), (uu____5528)))
end)) lbs (((Prims.parse_int "0")), ([])))
in (match (uu____5490) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____5568 = (FStar_List.fold_right (fun u uu____5586 -> (match (uu____5586) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____5568) with
| (uu____5609, u_let_rec_closing) -> begin
(

let uu___146_5615 = lb
in (

let uu____5616 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___146_5615.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___146_5615.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___146_5615.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___146_5615.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5616}))
end)))))
in (

let t1 = (subst let_rec_closing t)
in ((lbs1), (t1))))
end))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____5629 -> (match (uu____5629) with
| (us, t) -> begin
(

let n1 = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____5654 -> (match (uu____5654) with
| (x, uu____5660) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n1 - i)))))
end)) binders)
in (

let t1 = (subst s t)
in ((us), (t1))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____5677 -> (match (uu____5677) with
| (us', t) -> begin
(

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n1 - i)))))) us)
in (

let uu____5699 = (subst s t)
in ((us'), (uu____5699))))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n1 = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____5722 -> (match (uu____5722) with
| (x, uu____5728) -> begin
FStar_Syntax_Syntax.DB ((((n1 - i)), (x)))
end))))))


let closing_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (closing_subst bs))




