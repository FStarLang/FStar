
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
| uu____689 -> begin
t
end))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(

let uu____703 = (FStar_Syntax_Unionfind.univ_find u')
in (match (uu____703) with
| FStar_Pervasives_Native.Some (u1) -> begin
(compress_univ u1)
end
| uu____707 -> begin
u
end))
end
| uu____710 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___104_729 -> (match (uu___104_729) with
| FStar_Syntax_Syntax.DB (i, x) when (Prims.op_Equality i a.FStar_Syntax_Syntax.index) -> begin
(

let uu____734 = (

let uu____735 = (

let uu____736 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x uu____736))
in (FStar_Syntax_Syntax.bv_to_name uu____735))
in FStar_Pervasives_Native.Some (uu____734))
end
| uu____737 -> begin
FStar_Pervasives_Native.None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___105_756 -> (match (uu___105_756) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____761 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___109_764 = a
in {FStar_Syntax_Syntax.ppname = uu___109_764.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___109_764.FStar_Syntax_Syntax.sort}))
in FStar_Pervasives_Native.Some (uu____761))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____773 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___106_791 -> (match (uu___106_791) with
| FStar_Syntax_Syntax.UN (y, t) when (Prims.op_Equality x y) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____796 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___107_814 -> (match (uu___107_814) with
| FStar_Syntax_Syntax.UD (y, i) when (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____819 -> begin
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
| FStar_Syntax_Syntax.U_unif (uu____843) -> begin
u1
end
| FStar_Syntax_Syntax.U_succ (u2) -> begin
(

let uu____853 = (subst_univ s u2)
in FStar_Syntax_Syntax.U_succ (uu____853))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____857 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (uu____857))
end)))


let tag_with_range : 'Auu____866 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ('Auu____866 * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t s -> (match ((FStar_Pervasives_Native.snd s)) with
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

let uu____899 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_bvar (uu____899))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____901 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_name (uu____901))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v1 = (

let uu___110_907 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1); FStar_Syntax_Syntax.p = uu___110_907.FStar_Syntax_Syntax.p})
in (

let fv1 = (

let uu___111_909 = fv
in {FStar_Syntax_Syntax.fv_name = v1; FStar_Syntax_Syntax.fv_delta = uu___111_909.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___111_909.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv1))))
end
| t' -> begin
t'
end)
in (

let uu___112_911 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___112_911.FStar_Syntax_Syntax.vars})))
end))


let tag_lid_with_range : 'Auu____920 . FStar_Ident.lident  ->  ('Auu____920 * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Ident.lident = (fun l s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____944 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r)
in (FStar_Ident.set_lid_range l uu____944))
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
| uu____1062 -> begin
(

let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1072) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1077) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1082) -> begin
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

let uu____1191 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (

let uu____1192 = (

let uu____1195 = (

let uu____1196 = (subst_univ (FStar_Pervasives_Native.fst s) u)
in FStar_Syntax_Syntax.Tm_type (uu____1196))
in (FStar_Syntax_Syntax.mk uu____1195))
in (uu____1192 FStar_Pervasives_Native.None uu____1191)))
end
| uu____1206 -> begin
(

let uu____1207 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed ((t0), (s)) uu____1207))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___108_1221 -> (match (uu___108_1221) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(

let uu____1225 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (uu____1225))
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
| uu____1259 -> begin
(

let uu___113_1270 = t
in (

let uu____1271 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____1278 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____1283 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____1286 = (FStar_List.map (fun uu____1311 -> (match (uu____1311) with
| (t1, imp) -> begin
(

let uu____1330 = (subst' s t1)
in ((uu____1330), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (

let uu____1335 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu____1271; FStar_Syntax_Syntax.effect_name = uu____1278; FStar_Syntax_Syntax.result_typ = uu____1283; FStar_Syntax_Syntax.effect_args = uu____1286; FStar_Syntax_Syntax.flags = uu____1335}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([], FStar_Pervasives_Native.None) -> begin
t
end
| (([])::[], FStar_Pervasives_Native.None) -> begin
t
end
| uu____1372 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uopt) -> begin
(

let uu____1395 = (subst' s t1)
in (

let uu____1396 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____1395 uu____1396)))
end
| FStar_Syntax_Syntax.GTotal (t1, uopt) -> begin
(

let uu____1415 = (subst' s t1)
in (

let uu____1416 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1415 uu____1416)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1426 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp uu____1426))
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
| FStar_Syntax_Syntax.NT (uu____1443) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n1 s -> (FStar_List.map (shift n1) s))


let shift_subst' : 'Auu____1464 . Prims.int  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1464)  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1464) = (fun n1 s -> (

let uu____1491 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (shift_subst n1)))
in ((uu____1491), ((FStar_Pervasives_Native.snd s)))))


let subst_binder' : 'Auu____1510 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.bv * 'Auu____1510)  ->  (FStar_Syntax_Syntax.bv * 'Auu____1510) = (fun s uu____1526 -> (match (uu____1526) with
| (x, imp) -> begin
(

let uu____1533 = (

let uu___114_1534 = x
in (

let uu____1535 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___114_1534.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___114_1534.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1535}))
in ((uu____1533), (imp)))
end))


let subst_binders' : 'Auu____1544 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.bv * 'Auu____1544) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____1544) Prims.list = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1603 -> begin
(

let uu____1604 = (shift_subst' i s)
in (subst_binder' uu____1604 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (FStar_Pervasives_Native.None)) bs))


let subst_arg' : 'Auu____1635 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1635)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1635) = (fun s uu____1655 -> (match (uu____1655) with
| (t, imp) -> begin
(

let uu____1668 = (subst' s t)
in ((uu____1668), (imp)))
end))


let subst_args' : 'Auu____1678 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1678) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1678) Prims.list = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____1768) -> begin
((p1), (n1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1789 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1843 uu____1844 -> (match (((uu____1843), (uu____1844))) with
| ((pats1, n2), (p2, imp)) -> begin
(

let uu____1923 = (aux n2 p2)
in (match (uu____1923) with
| (p3, m) -> begin
(((((p3), (imp)))::pats1), (m))
end))
end)) (([]), (n1))))
in (match (uu____1789) with
| (pats1, n2) -> begin
(((

let uu___115_1981 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___115_1981.FStar_Syntax_Syntax.p})), (n2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___116_2007 = x
in (

let uu____2008 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___116_2007.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___116_2007.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2008}))
in (((

let uu___117_2014 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___117_2014.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___118_2030 = x
in (

let uu____2031 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___118_2030.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_2030.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2031}))
in (((

let uu___119_2037 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___119_2037.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___120_2058 = x
in (

let uu____2059 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___120_2058.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___120_2058.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2059}))
in (

let t01 = (subst' s1 t0)
in (((

let uu___121_2068 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___121_2068.FStar_Syntax_Syntax.p})), (n1)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s lopt -> (match (lopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____2090 = (

let uu___122_2091 = rc
in (

let uu____2092 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (subst' s))
in {FStar_Syntax_Syntax.residual_effect = uu___122_2091.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____2092; FStar_Syntax_Syntax.residual_flags = uu___122_2091.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____2090))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk1 = (fun t' -> (

let uu____2121 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2121)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2124) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_constant (uu____2151) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2156) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2165) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_type (uu____2186) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2187) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_name (uu____2188) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us1 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us)
in (

let uu____2204 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us1)
in (tag_with_range uu____2204 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(

let uu____2233 = (

let uu____2234 = (

let uu____2249 = (subst' s t0)
in (

let uu____2252 = (subst_args' s args)
in ((uu____2249), (uu____2252))))
in FStar_Syntax_Syntax.Tm_app (uu____2234))
in (mk1 uu____2233))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t1) -> begin
(

let uu____2347 = (subst' s t1)
in FStar_Util.Inl (uu____2347))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2361 = (subst_comp' s c)
in FStar_Util.Inr (uu____2361))
end)
in (

let uu____2368 = (

let uu____2369 = (

let uu____2396 = (subst' s t0)
in (

let uu____2399 = (

let uu____2416 = (FStar_Util.map_opt topt (subst' s))
in ((annot1), (uu____2416)))
in ((uu____2396), (uu____2399), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2369))
in (mk1 uu____2368)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n1 = (FStar_List.length bs)
in (

let s' = (shift_subst' n1 s)
in (

let uu____2500 = (

let uu____2501 = (

let uu____2518 = (subst_binders' s bs)
in (

let uu____2525 = (subst' s' body)
in (

let uu____2528 = (push_subst_lcomp s' lopt)
in ((uu____2518), (uu____2525), (uu____2528)))))
in FStar_Syntax_Syntax.Tm_abs (uu____2501))
in (mk1 uu____2500))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n1 = (FStar_List.length bs)
in (

let uu____2564 = (

let uu____2565 = (

let uu____2578 = (subst_binders' s bs)
in (

let uu____2585 = (

let uu____2588 = (shift_subst' n1 s)
in (subst_comp' uu____2588 comp))
in ((uu____2578), (uu____2585))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2565))
in (mk1 uu____2564)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x1 = (

let uu___123_2620 = x
in (

let uu____2621 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___123_2620.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_2620.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2621}))
in (

let phi1 = (

let uu____2627 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____2627 phi))
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((x1), (phi1)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t01 = (subst' s t0)
in (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____2754 -> (match (uu____2754) with
| (pat, wopt, branch) -> begin
(

let uu____2800 = (subst_pat' s pat)
in (match (uu____2800) with
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

let uu____2848 = (subst' s1 w)
in FStar_Pervasives_Native.Some (uu____2848))
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

let uu____2933 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____2933) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____2936 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___124_2948 = x
in {FStar_Syntax_Syntax.ppname = uu___124_2948.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___124_2948.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr (fv)
end)
in (

let uu___125_2950 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___125_2950.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___125_2950.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (mk1 (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs1))), (body1)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let uu____2977 = (

let uu____2978 = (

let uu____2985 = (subst' s t0)
in (

let uu____2988 = (

let uu____2989 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____2989))
in ((uu____2985), (uu____2988))))
in FStar_Syntax_Syntax.Tm_meta (uu____2978))
in (mk1 uu____2977))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) -> begin
(

let uu____3049 = (

let uu____3050 = (

let uu____3057 = (subst' s t0)
in (

let uu____3060 = (

let uu____3061 = (

let uu____3068 = (subst' s t1)
in ((m), (uu____3068)))
in FStar_Syntax_Syntax.Meta_monadic (uu____3061))
in ((uu____3057), (uu____3060))))
in FStar_Syntax_Syntax.Tm_meta (uu____3050))
in (mk1 uu____3049))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) -> begin
(

let uu____3087 = (

let uu____3088 = (

let uu____3095 = (subst' s t0)
in (

let uu____3098 = (

let uu____3099 = (

let uu____3108 = (subst' s t1)
in ((m1), (m2), (uu____3108)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____3099))
in ((uu____3095), (uu____3098))))
in FStar_Syntax_Syntax.Tm_meta (uu____3088))
in (mk1 uu____3087))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____3121 = (

let uu____3122 = (

let uu____3129 = (subst' s t1)
in ((uu____3129), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____3122))
in (mk1 uu____3121))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (force_delayed_thunk t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t2, s), memo) -> begin
(

let t' = (

let uu____3193 = (push_subst s t2)
in (compress uu____3193))
in ((FStar_Syntax_Unionfind.update_in_tx memo (FStar_Pervasives_Native.Some (t')));
t';
))
end
| uu____3213 -> begin
(

let t' = (force_uvar t1)
in (match (t'.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____3217) -> begin
(compress t')
end
| uu____3242 -> begin
t'
end))
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (subst' (([]), (FStar_Pervasives_Native.Some ((

let uu___126_3282 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = uu___126_3282.FStar_Range.use_range})))) t))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let closing_subst : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun bs -> (

let uu____3311 = (FStar_List.fold_right (fun uu____3334 uu____3335 -> (match (((uu____3334), (uu____3335))) with
| ((x, uu____3363), (subst1, n1)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n1))))::subst1), ((n1 + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____3311 FStar_Pervasives_Native.fst)))


let open_binders' : 'Auu____3398 . (FStar_Syntax_Syntax.bv * 'Auu____3398) Prims.list  ->  ((FStar_Syntax_Syntax.bv * 'Auu____3398) Prims.list * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun bs -> (

let rec aux = (fun bs1 o -> (match (bs1) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___127_3504 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____3505 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___127_3504.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___127_3504.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3505}))
in (

let o1 = (

let uu____3511 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____3511)
in (

let uu____3514 = (aux bs' o1)
in (match (uu____3514) with
| (bs'1, o2) -> begin
(((((x'), (imp)))::bs'1), (o2))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____3573 = (open_binders' bs)
in (FStar_Pervasives_Native.fst uu____3573)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____3608 = (open_binders' bs)
in (match (uu____3608) with
| (bs', opening) -> begin
(

let uu____3645 = (subst opening t)
in ((bs'), (uu____3645), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____3666 = (open_term' bs t)
in (match (uu____3666) with
| (b, t1, uu____3679) -> begin
((b), (t1))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____3692 = (open_binders' bs)
in (match (uu____3692) with
| (bs', opening) -> begin
(

let uu____3727 = (subst_comp opening t)
in ((bs'), (uu____3727)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec open_pat_aux = (fun sub1 renaming p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____3808) -> begin
((p1), (sub1), (renaming))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3837 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____3929 uu____3930 -> (match (((uu____3929), (uu____3930))) with
| ((pats1, sub2, renaming1), (p2, imp)) -> begin
(

let uu____4078 = (open_pat_aux sub2 renaming1 p2)
in (match (uu____4078) with
| (p3, sub3, renaming2) -> begin
(((((p3), (imp)))::pats1), (sub3), (renaming2))
end))
end)) (([]), (sub1), (renaming))))
in (match (uu____3837) with
| (pats1, sub2, renaming1) -> begin
(((

let uu___128_4248 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___128_4248.FStar_Syntax_Syntax.p})), (sub2), (renaming1))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___129_4267 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4268 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___129_4267.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___129_4267.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4268}))
in (

let sub2 = (

let uu____4274 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4274)
in (((

let uu___130_4288 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.p = uu___130_4288.FStar_Syntax_Syntax.p})), (sub2), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___131_4297 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4298 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___131_4297.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_4297.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4298}))
in (

let sub2 = (

let uu____4304 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4304)
in (((

let uu___132_4318 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.p = uu___132_4318.FStar_Syntax_Syntax.p})), (sub2), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___133_4332 = x
in (

let uu____4333 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___133_4332.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_4332.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4333}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___134_4348 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___134_4348.FStar_Syntax_Syntax.p})), (sub1), (renaming))))
end))
in (

let uu____4351 = (open_pat_aux [] [] p)
in (match (uu____4351) with
| (p1, sub1, uu____4378) -> begin
((p1), (sub1))
end))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____4406 -> (match (uu____4406) with
| (p, wopt, e) -> begin
(

let uu____4426 = (open_pat p)
in (match (uu____4426) with
| (p1, opening) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____4445 = (subst opening w)
in FStar_Pervasives_Native.Some (uu____4445))
end)
in (

let e1 = (subst opening e)
in ((p1), (wopt1), (e1))))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____4457 = (closing_subst bs)
in (subst uu____4457 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____4468 = (closing_subst bs)
in (subst_comp uu____4468 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs1 -> (match (bs1) with
| [] -> begin
[]
end
| ((x, imp))::tl1 -> begin
(

let x1 = (

let uu___135_4520 = x
in (

let uu____4521 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___135_4520.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___135_4520.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4521}))
in (

let s' = (

let uu____4527 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____4527)
in (

let uu____4530 = (aux s' tl1)
in (((x1), (imp)))::uu____4530)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let uu___136_4552 = lc
in (

let uu____4553 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___136_4552.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____4553; FStar_Syntax_Syntax.cflags = uu___136_4552.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____4558 -> (

let uu____4559 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s uu____4559)))}))))


let close_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4607) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4630 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4696 uu____4697 -> (match (((uu____4696), (uu____4697))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____4800 = (aux sub2 p2)
in (match (uu____4800) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4630) with
| (pats1, sub2) -> begin
(((

let uu___137_4902 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___137_4902.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___138_4921 = x
in (

let uu____4922 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___138_4921.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___138_4921.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4922}))
in (

let sub2 = (

let uu____4928 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____4928)
in (((

let uu___139_4936 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___139_4936.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___140_4941 = x
in (

let uu____4942 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___140_4941.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___140_4941.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4942}))
in (

let sub2 = (

let uu____4948 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____4948)
in (((

let uu___141_4956 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___141_4956.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___142_4966 = x
in (

let uu____4967 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___142_4966.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___142_4966.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4967}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___143_4976 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___143_4976.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____4982 -> (match (uu____4982) with
| (p, wopt, e) -> begin
(

let uu____5002 = (close_pat p)
in (match (uu____5002) with
| (p1, closing) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____5033 = (subst closing w)
in FStar_Pervasives_Native.Some (uu____5033))
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

let uu____5092 = (univ_var_opening us)
in (match (uu____5092) with
| (s, us') -> begin
(

let t1 = (subst s t)
in ((us'), (t1)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____5134 = (univ_var_opening us)
in (match (uu____5134) with
| (s, us') -> begin
(

let uu____5157 = (subst_comp s c)
in ((us'), (uu____5157)))
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

let uu____5207 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5207) with
| true -> begin
((lbs), (t))
end
| uu____5216 -> begin
(

let uu____5217 = (FStar_List.fold_right (fun lb uu____5245 -> (match (uu____5245) with
| (i, lbs1, out) -> begin
(

let x = (

let uu____5278 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____5278))
in (((i + (Prims.parse_int "1"))), (((

let uu___144_5284 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___144_5284.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___144_5284.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___144_5284.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___144_5284.FStar_Syntax_Syntax.lbdef}))::lbs1), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
in (match (uu____5217) with
| (n_let_recs, lbs1, let_rec_opening) -> begin
(

let lbs2 = (FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let uu____5321 = (FStar_List.fold_right (fun u uu____5348 -> (match (uu____5348) with
| (i, us, out) -> begin
(((i + (Prims.parse_int "1"))), ((u)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u)))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____5321) with
| (uu____5388, us, u_let_rec_opening) -> begin
(

let uu___145_5399 = lb
in (

let uu____5400 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___145_5399.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu___145_5399.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___145_5399.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5400}))
end)))))
in (

let t1 = (subst let_rec_opening t)
in ((lbs2), (t1))))
end))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____5424 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5424) with
| true -> begin
((lbs), (t))
end
| uu____5433 -> begin
(

let uu____5434 = (FStar_List.fold_right (fun lb uu____5453 -> (match (uu____5453) with
| (i, out) -> begin
(

let uu____5472 = (

let uu____5475 = (

let uu____5476 = (

let uu____5481 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____5481), (i)))
in FStar_Syntax_Syntax.NM (uu____5476))
in (uu____5475)::out)
in (((i + (Prims.parse_int "1"))), (uu____5472)))
end)) lbs (((Prims.parse_int "0")), ([])))
in (match (uu____5434) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____5512 = (FStar_List.fold_right (fun u uu____5530 -> (match (uu____5530) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____5512) with
| (uu____5553, u_let_rec_closing) -> begin
(

let uu___146_5559 = lb
in (

let uu____5560 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___146_5559.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___146_5559.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___146_5559.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___146_5559.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5560}))
end)))))
in (

let t1 = (subst let_rec_closing t)
in ((lbs1), (t1))))
end))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____5573 -> (match (uu____5573) with
| (us, t) -> begin
(

let n1 = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____5598 -> (match (uu____5598) with
| (x, uu____5604) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n1 - i)))))
end)) binders)
in (

let t1 = (subst s t)
in ((us), (t1))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____5621 -> (match (uu____5621) with
| (us', t) -> begin
(

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n1 - i)))))) us)
in (

let uu____5643 = (subst s t)
in ((us'), (uu____5643))))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n1 = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____5666 -> (match (uu____5666) with
| (x, uu____5672) -> begin
FStar_Syntax_Syntax.DB ((((n1 - i)), (x)))
end))))))


let closing_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (closing_subst bs))




