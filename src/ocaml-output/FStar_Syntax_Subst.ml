
open Prims
open FStar_Pervasives

let subst_to_string = (fun s -> (

let uu____16 = (FStar_All.pipe_right s (FStar_List.map (fun uu____27 -> (match (uu____27) with
| (b, uu____31) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right uu____16 (FStar_String.concat ", "))))


let rec apply_until_some = (fun f s -> (match (s) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (s0)::rest -> begin
(

let uu____70 = (f s0)
in (match (uu____70) with
| FStar_Pervasives_Native.None -> begin
(apply_until_some f rest)
end
| FStar_Pervasives_Native.Some (st) -> begin
FStar_Pervasives_Native.Some (((rest), (st)))
end))
end))


let map_some_curry = (fun f x uu___103_116 -> (match (uu___103_116) with
| FStar_Pervasives_Native.None -> begin
x
end
| FStar_Pervasives_Native.Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map = (fun f s g t -> (

let uu____184 = (apply_until_some f s)
in (FStar_All.pipe_right uu____184 (map_some_curry g t))))


let compose_subst = (fun s1 s2 -> (

let s = (FStar_List.append (FStar_Pervasives_Native.fst s1) (FStar_Pervasives_Native.fst s2))
in (

let ropt = (match ((FStar_Pervasives_Native.snd s2)) with
| FStar_Pervasives_Native.Some (uu____243) -> begin
(FStar_Pervasives_Native.snd s2)
end
| uu____246 -> begin
(FStar_Pervasives_Native.snd s1)
end)
in ((s), (ropt)))))


let delay : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term = (fun t s -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t'), ((compose_subst s' s))) t.FStar_Syntax_Syntax.pos)
end
| uu____314 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t), (s)) t.FStar_Syntax_Syntax.pos)
end))


let rec force_uvar' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____335) -> begin
(

let uu____352 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____352) with
| FStar_Pervasives_Native.Some (t') -> begin
(force_uvar' t')
end
| uu____357 -> begin
t
end))
end
| uu____359 -> begin
t
end))


let force_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (

let t' = (force_uvar' t)
in (

let uu____373 = (FStar_Util.physical_equality t t')
in (match (uu____373) with
| true -> begin
t
end
| uu____378 -> begin
(delay t' (([]), (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))))
end))))


let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(

let uu____421 = (FStar_ST.read m)
in (match (uu____421) with
| FStar_Pervasives_Native.None -> begin
t
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let t'1 = (force_delayed_thunk t')
in ((FStar_ST.write m (FStar_Pervasives_Native.Some (t'1)));
t'1;
))
end))
end
| uu____450 -> begin
t
end))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(

let uu____460 = (FStar_Syntax_Unionfind.univ_find u')
in (match (uu____460) with
| FStar_Pervasives_Native.Some (u1) -> begin
(compress_univ u1)
end
| uu____463 -> begin
u
end))
end
| uu____465 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___104_481 -> (match (uu___104_481) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(

let uu____485 = (

let uu____486 = (

let uu____487 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x uu____487))
in (FStar_Syntax_Syntax.bv_to_name uu____486))
in FStar_Pervasives_Native.Some (uu____485))
end
| uu____488 -> begin
FStar_Pervasives_Native.None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___105_504 -> (match (uu___105_504) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____508 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___109_511 = a
in {FStar_Syntax_Syntax.ppname = uu___109_511.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___109_511.FStar_Syntax_Syntax.sort}))
in FStar_Pervasives_Native.Some (uu____508))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____520 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___106_535 -> (match (uu___106_535) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____539 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___107_554 -> (match (uu___107_554) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____558 -> begin
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
| FStar_Syntax_Syntax.U_unif (uu____576) -> begin
u1
end
| FStar_Syntax_Syntax.U_succ (u2) -> begin
(

let uu____582 = (subst_univ s u2)
in FStar_Syntax_Syntax.U_succ (uu____582))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____585 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (uu____585))
end)))


let tag_with_range = (fun t s -> (match ((FStar_Pervasives_Native.snd s)) with
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

let uu____622 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_bvar (uu____622))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____624 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_name (uu____624))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v1 = (

let uu___110_629 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1); FStar_Syntax_Syntax.p = uu___110_629.FStar_Syntax_Syntax.p})
in (

let fv1 = (

let uu___111_631 = fv
in {FStar_Syntax_Syntax.fv_name = v1; FStar_Syntax_Syntax.fv_delta = uu___111_631.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___111_631.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv1))))
end
| t' -> begin
t'
end)
in (

let uu___112_633 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.tk = uu___112_633.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___112_633.FStar_Syntax_Syntax.vars})))
end))


let tag_lid_with_range = (fun l s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____663 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r)
in (FStar_Ident.set_lid_range l uu____663))
end))


let mk_range : FStar_Range.range  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Range.range = (fun r s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
r
end
| FStar_Pervasives_Native.Some (r') -> begin
(FStar_Range.set_use_range r r')
end))


let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (

let subst_tail = (fun tl1 -> (subst' ((tl1), ((FStar_Pervasives_Native.snd s)))))
in (match (s) with
| ([], FStar_Pervasives_Native.None) -> begin
t
end
| (([])::[], FStar_Pervasives_Native.None) -> begin
t
end
| uu____747 -> begin
(

let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_constant (uu____755) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____758) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____761) -> begin
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

let uu____829 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (

let uu____830 = (

let uu____833 = (

let uu____834 = (subst_univ (FStar_Pervasives_Native.fst s) u)
in FStar_Syntax_Syntax.Tm_type (uu____834))
in (FStar_Syntax_Syntax.mk uu____833))
in (uu____830 FStar_Pervasives_Native.None uu____829)))
end
| uu____846 -> begin
(

let uu____847 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed ((t0), (s)) uu____847))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___108_858 -> (match (uu___108_858) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(

let uu____862 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (uu____862))
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
| uu____882 -> begin
(

let uu___113_888 = t
in (

let uu____889 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____893 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____896 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____899 = (FStar_List.map (fun uu____917 -> (match (uu____917) with
| (t1, imp) -> begin
(

let uu____932 = (subst' s t1)
in ((uu____932), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (

let uu____937 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu____889; FStar_Syntax_Syntax.effect_name = uu____893; FStar_Syntax_Syntax.result_typ = uu____896; FStar_Syntax_Syntax.effect_args = uu____899; FStar_Syntax_Syntax.flags = uu____937}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([], FStar_Pervasives_Native.None) -> begin
t
end
| (([])::[], FStar_Pervasives_Native.None) -> begin
t
end
| uu____959 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uopt) -> begin
(

let uu____975 = (subst' s t1)
in (

let uu____976 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____975 uu____976)))
end
| FStar_Syntax_Syntax.GTotal (t1, uopt) -> begin
(

let uu____989 = (subst' s t1)
in (

let uu____990 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____989 uu____990)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____996 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp uu____996))
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
| FStar_Syntax_Syntax.NT (uu____1013) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n1 s -> (FStar_List.map (shift n1) s))


let shift_subst' = (fun n1 s -> (

let uu____1050 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (shift_subst n1)))
in ((uu____1050), ((FStar_Pervasives_Native.snd s)))))


let subst_binder' = (fun s uu____1075 -> (match (uu____1075) with
| (x, imp) -> begin
(

let uu____1080 = (

let uu___114_1081 = x
in (

let uu____1082 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___114_1081.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___114_1081.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1082}))
in ((uu____1080), (imp)))
end))


let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((i = (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1127 -> begin
(

let uu____1128 = (shift_subst' i s)
in (subst_binder' uu____1128 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (FStar_Pervasives_Native.None)) bs))


let subst_arg' = (fun s uu____1167 -> (match (uu____1167) with
| (t, imp) -> begin
(

let uu____1178 = (subst' s t)
in ((uu____1178), (imp)))
end))


let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____1248) -> begin
((p1), (n1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1260 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1292 uu____1293 -> (match (((uu____1292), (uu____1293))) with
| ((pats1, n2), (p2, imp)) -> begin
(

let uu____1335 = (aux n2 p2)
in (match (uu____1335) with
| (p3, m) -> begin
(((((p3), (imp)))::pats1), (m))
end))
end)) (([]), (n1))))
in (match (uu____1260) with
| (pats1, n2) -> begin
(((

let uu___115_1367 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___115_1367.FStar_Syntax_Syntax.p})), (n2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___116_1382 = x
in (

let uu____1383 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___116_1382.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___116_1382.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1383}))
in (((

let uu___117_1388 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___117_1388.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___118_1398 = x
in (

let uu____1399 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___118_1398.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_1398.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1399}))
in (((

let uu___119_1404 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___119_1404.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___120_1419 = x
in (

let uu____1420 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___120_1419.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___120_1419.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1420}))
in (

let t01 = (subst' s1 t0)
in (((

let uu___121_1428 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___121_1428.FStar_Syntax_Syntax.p})), (n1)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s lopt -> (match (lopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____1445 = (

let uu___122_1446 = rc
in (

let uu____1447 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (subst' s))
in {FStar_Syntax_Syntax.residual_effect = uu___122_1446.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____1447; FStar_Syntax_Syntax.residual_flags = uu___122_1446.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____1445))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk1 = (fun t' -> (

let uu____1475 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____1475)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1482) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_constant (uu____1499) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1502) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1507) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_type (uu____1520) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1521) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_name (uu____1522) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us1 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us)
in (

let uu____1534 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us1)
in (tag_with_range uu____1534 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(

let uu____1555 = (

let uu____1556 = (

let uu____1566 = (subst' s t0)
in (

let uu____1569 = (subst_args' s args)
in ((uu____1566), (uu____1569))))
in FStar_Syntax_Syntax.Tm_app (uu____1556))
in (mk1 uu____1555))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t1) -> begin
(

let uu____1641 = (subst' s t1)
in FStar_Util.Inl (uu____1641))
end
| FStar_Util.Inr (c) -> begin
(

let uu____1655 = (subst_comp' s c)
in FStar_Util.Inr (uu____1655))
end)
in (

let uu____1662 = (

let uu____1663 = (

let uu____1681 = (subst' s t0)
in (

let uu____1684 = (

let uu____1696 = (FStar_Util.map_opt topt (subst' s))
in ((annot1), (uu____1696)))
in ((uu____1681), (uu____1684), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____1663))
in (mk1 uu____1662)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n1 = (FStar_List.length bs)
in (

let s' = (shift_subst' n1 s)
in (

let uu____1757 = (

let uu____1758 = (

let uu____1768 = (subst_binders' s bs)
in (

let uu____1772 = (subst' s' body)
in (

let uu____1775 = (push_subst_lcomp s' lopt)
in ((uu____1768), (uu____1772), (uu____1775)))))
in FStar_Syntax_Syntax.Tm_abs (uu____1758))
in (mk1 uu____1757))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n1 = (FStar_List.length bs)
in (

let uu____1800 = (

let uu____1801 = (

let uu____1809 = (subst_binders' s bs)
in (

let uu____1813 = (

let uu____1816 = (shift_subst' n1 s)
in (subst_comp' uu____1816 comp))
in ((uu____1809), (uu____1813))))
in FStar_Syntax_Syntax.Tm_arrow (uu____1801))
in (mk1 uu____1800)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x1 = (

let uu___123_1839 = x
in (

let uu____1840 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___123_1839.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_1839.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1840}))
in (

let phi1 = (

let uu____1846 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____1846 phi))
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((x1), (phi1)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t01 = (subst' s t0)
in (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____1935 -> (match (uu____1935) with
| (pat, wopt, branch) -> begin
(

let uu____1968 = (subst_pat' s pat)
in (match (uu____1968) with
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

let uu____2003 = (subst' s1 w)
in FStar_Pervasives_Native.Some (uu____2003))
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

let uu____2071 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____2071) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____2074 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___124_2082 = x
in {FStar_Syntax_Syntax.ppname = uu___124_2082.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___124_2082.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr (fv)
end)
in (

let uu___125_2084 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___125_2084.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___125_2084.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (mk1 (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs1))), (body1)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let uu____2103 = (

let uu____2104 = (

let uu____2109 = (subst' s t0)
in (

let uu____2112 = (

let uu____2113 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____2113))
in ((uu____2109), (uu____2112))))
in FStar_Syntax_Syntax.Tm_meta (uu____2104))
in (mk1 uu____2103))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) -> begin
(

let uu____2155 = (

let uu____2156 = (

let uu____2161 = (subst' s t0)
in (

let uu____2164 = (

let uu____2165 = (

let uu____2170 = (subst' s t1)
in ((m), (uu____2170)))
in FStar_Syntax_Syntax.Meta_monadic (uu____2165))
in ((uu____2161), (uu____2164))))
in FStar_Syntax_Syntax.Tm_meta (uu____2156))
in (mk1 uu____2155))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) -> begin
(

let uu____2189 = (

let uu____2190 = (

let uu____2195 = (subst' s t0)
in (

let uu____2198 = (

let uu____2199 = (

let uu____2205 = (subst' s t1)
in ((m1), (m2), (uu____2205)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____2199))
in ((uu____2195), (uu____2198))))
in FStar_Syntax_Syntax.Tm_meta (uu____2190))
in (mk1 uu____2189))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____2218 = (

let uu____2219 = (

let uu____2224 = (subst' s t1)
in ((uu____2224), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____2219))
in (mk1 uu____2218))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (force_delayed_thunk t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t2, s), memo) -> begin
(

let t' = (

let uu____2269 = (push_subst s t2)
in (compress uu____2269))
in ((FStar_Syntax_Unionfind.update_in_tx memo (FStar_Pervasives_Native.Some (t')));
t';
))
end
| uu____2276 -> begin
(

let t' = (force_uvar t1)
in (match (t'.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2280) -> begin
(compress t')
end
| uu____2295 -> begin
t'
end))
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (subst' (([]), (FStar_Pervasives_Native.Some ((

let uu___126_2324 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = uu___126_2324.FStar_Range.use_range})))) t))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let closing_subst : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun bs -> (

let uu____2345 = (FStar_List.fold_right (fun uu____2360 uu____2361 -> (match (((uu____2360), (uu____2361))) with
| ((x, uu____2376), (subst1, n1)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n1))))::subst1), ((n1 + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____2345 FStar_Pervasives_Native.fst)))


let open_binders' = (fun bs -> (

let rec aux = (fun bs1 o -> (match (bs1) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___127_2458 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____2459 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___127_2458.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___127_2458.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2459}))
in (

let o1 = (

let uu____2464 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____2464)
in (

let uu____2466 = (aux bs' o1)
in (match (uu____2466) with
| (bs'1, o2) -> begin
(((((x'), (imp)))::bs'1), (o2))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____2499 = (open_binders' bs)
in (FStar_Pervasives_Native.fst uu____2499)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____2521 = (open_binders' bs)
in (match (uu____2521) with
| (bs', opening) -> begin
(

let uu____2541 = (subst opening t)
in ((bs'), (uu____2541), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____2556 = (open_term' bs t)
in (match (uu____2556) with
| (b, t1, uu____2564) -> begin
((b), (t1))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____2575 = (open_binders' bs)
in (match (uu____2575) with
| (bs', opening) -> begin
(

let uu____2594 = (subst_comp opening t)
in ((bs'), (uu____2594)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec open_pat_aux = (fun sub1 renaming p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____2642) -> begin
((p1), (sub1), (renaming))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2658 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____2710 uu____2711 -> (match (((uu____2710), (uu____2711))) with
| ((pats1, sub2, renaming1), (p2, imp)) -> begin
(

let uu____2788 = (open_pat_aux sub2 renaming1 p2)
in (match (uu____2788) with
| (p3, sub3, renaming2) -> begin
(((((p3), (imp)))::pats1), (sub3), (renaming2))
end))
end)) (([]), (sub1), (renaming))))
in (match (uu____2658) with
| (pats1, sub2, renaming1) -> begin
(((

let uu___128_2877 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___128_2877.FStar_Syntax_Syntax.p})), (sub2), (renaming1))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___129_2888 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____2889 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___129_2888.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___129_2888.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2889}))
in (

let sub2 = (

let uu____2894 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____2894)
in (((

let uu___130_2902 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.p = uu___130_2902.FStar_Syntax_Syntax.p})), (sub2), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___131_2908 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____2909 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___131_2908.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_2908.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2909}))
in (

let sub2 = (

let uu____2914 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____2914)
in (((

let uu___132_2922 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.p = uu___132_2922.FStar_Syntax_Syntax.p})), (sub2), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___133_2933 = x
in (

let uu____2934 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___133_2933.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_2933.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2934}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___134_2944 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___134_2944.FStar_Syntax_Syntax.p})), (sub1), (renaming))))
end))
in (

let uu____2946 = (open_pat_aux [] [] p)
in (match (uu____2946) with
| (p1, sub1, uu____2961) -> begin
((p1), (sub1))
end))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____2977 -> (match (uu____2977) with
| (p, wopt, e) -> begin
(

let uu____2993 = (open_pat p)
in (match (uu____2993) with
| (p1, opening) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____3008 = (subst opening w)
in FStar_Pervasives_Native.Some (uu____3008))
end)
in (

let e1 = (subst opening e)
in ((p1), (wopt1), (e1))))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____3019 = (closing_subst bs)
in (subst uu____3019 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____3029 = (closing_subst bs)
in (subst_comp uu____3029 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs1 -> (match (bs1) with
| [] -> begin
[]
end
| ((x, imp))::tl1 -> begin
(

let x1 = (

let uu___135_3063 = x
in (

let uu____3064 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___135_3063.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___135_3063.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3064}))
in (

let s' = (

let uu____3069 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____3069)
in (

let uu____3071 = (aux s' tl1)
in (((x1), (imp)))::uu____3071)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let uu___136_3087 = lc
in (

let uu____3088 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___136_3087.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____3088; FStar_Syntax_Syntax.cflags = uu___136_3087.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____3093 -> (

let uu____3094 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s uu____3094)))}))))


let close_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____3124) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3137 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____3175 uu____3176 -> (match (((uu____3175), (uu____3176))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____3230 = (aux sub2 p2)
in (match (uu____3230) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____3137) with
| (pats1, sub2) -> begin
(((

let uu___137_3284 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___137_3284.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___138_3295 = x
in (

let uu____3296 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___138_3295.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___138_3295.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3296}))
in (

let sub2 = (

let uu____3301 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____3301)
in (((

let uu___139_3306 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___139_3306.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___140_3310 = x
in (

let uu____3311 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___140_3310.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___140_3310.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3311}))
in (

let sub2 = (

let uu____3316 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____3316)
in (((

let uu___141_3321 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___141_3321.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___142_3330 = x
in (

let uu____3331 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___142_3330.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___142_3330.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3331}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___143_3338 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___143_3338.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____3343 -> (match (uu____3343) with
| (p, wopt, e) -> begin
(

let uu____3359 = (close_pat p)
in (match (uu____3359) with
| (p1, closing) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____3380 = (subst closing w)
in FStar_Pervasives_Native.Some (uu____3380))
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

let uu____3436 = (univ_var_opening us)
in (match (uu____3436) with
| (s, us') -> begin
(

let t1 = (subst s t)
in ((us'), (t1)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____3463 = (univ_var_opening us)
in (match (uu____3463) with
| (s, us') -> begin
(

let uu____3476 = (subst_comp s c)
in ((us'), (uu____3476)))
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

let uu____3523 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____3523) with
| true -> begin
((lbs), (t))
end
| uu____3528 -> begin
(

let uu____3529 = (FStar_List.fold_right (fun lb uu____3547 -> (match (uu____3547) with
| (i, lbs1, out) -> begin
(

let x = (

let uu____3566 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____3566))
in (((i + (Prims.parse_int "1"))), (((

let uu___144_3570 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___144_3570.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___144_3570.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___144_3570.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___144_3570.FStar_Syntax_Syntax.lbdef}))::lbs1), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
in (match (uu____3529) with
| (n_let_recs, lbs1, let_rec_opening) -> begin
(

let lbs2 = (FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let uu____3595 = (FStar_List.fold_right (fun u uu____3612 -> (match (uu____3612) with
| (i, us, out) -> begin
(((i + (Prims.parse_int "1"))), ((u)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u)))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____3595) with
| (uu____3634, us, u_let_rec_opening) -> begin
(

let uu___145_3641 = lb
in (

let uu____3642 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___145_3641.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu___145_3641.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___145_3641.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____3642}))
end)))))
in (

let t1 = (subst let_rec_opening t)
in ((lbs2), (t1))))
end))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____3660 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____3660) with
| true -> begin
((lbs), (t))
end
| uu____3665 -> begin
(

let uu____3666 = (FStar_List.fold_right (fun lb uu____3679 -> (match (uu____3679) with
| (i, out) -> begin
(

let uu____3690 = (

let uu____3692 = (

let uu____3693 = (

let uu____3696 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____3696), (i)))
in FStar_Syntax_Syntax.NM (uu____3693))
in (uu____3692)::out)
in (((i + (Prims.parse_int "1"))), (uu____3690)))
end)) lbs (((Prims.parse_int "0")), ([])))
in (match (uu____3666) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____3717 = (FStar_List.fold_right (fun u uu____3729 -> (match (uu____3729) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____3717) with
| (uu____3742, u_let_rec_closing) -> begin
(

let uu___146_3746 = lb
in (

let uu____3747 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___146_3746.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___146_3746.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___146_3746.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___146_3746.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____3747}))
end)))))
in (

let t1 = (subst let_rec_closing t)
in ((lbs1), (t1))))
end))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____3759 -> (match (uu____3759) with
| (us, t) -> begin
(

let n1 = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____3785 -> (match (uu____3785) with
| (x, uu____3789) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n1 - i)))))
end)) binders)
in (

let t1 = (subst s t)
in ((us), (t1))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____3805 -> (match (uu____3805) with
| (us', t) -> begin
(

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n1 - i)))))) us)
in (

let uu____3832 = (subst s t)
in ((us'), (uu____3832))))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n1 = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____3855 -> (match (uu____3855) with
| (x, uu____3859) -> begin
FStar_Syntax_Syntax.DB ((((n1 - i)), (x)))
end))))))


let closing_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (closing_subst bs))




