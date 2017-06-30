
open Prims
open FStar_Pervasives

let subst_to_string = (fun s -> (

let uu____14 = (FStar_All.pipe_right s (FStar_List.map (fun uu____22 -> (match (uu____22) with
| (b, uu____26) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right uu____14 (FStar_String.concat ", "))))


let rec apply_until_some = (fun f s -> (match (s) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (s0)::rest -> begin
(

let uu____61 = (f s0)
in (match (uu____61) with
| FStar_Pervasives_Native.None -> begin
(apply_until_some f rest)
end
| FStar_Pervasives_Native.Some (st) -> begin
FStar_Pervasives_Native.Some (((rest), (st)))
end))
end))


let map_some_curry = (fun f x uu___99_101 -> (match (uu___99_101) with
| FStar_Pervasives_Native.None -> begin
x
end
| FStar_Pervasives_Native.Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map = (fun f s g t -> (

let uu____162 = (apply_until_some f s)
in (FStar_All.pipe_right uu____162 (map_some_curry g t))))


let compose_subst = (fun s1 s2 -> (

let s = (FStar_List.append (FStar_Pervasives_Native.fst s1) (FStar_Pervasives_Native.fst s2))
in (

let ropt = (match ((FStar_Pervasives_Native.snd s2)) with
| FStar_Pervasives_Native.Some (uu____217) -> begin
(FStar_Pervasives_Native.snd s2)
end
| uu____220 -> begin
(FStar_Pervasives_Native.snd s1)
end)
in ((s), (ropt)))))


let delay : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term = (fun t s -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t'), ((compose_subst s' s))))) t.FStar_Syntax_Syntax.pos)
end
| uu____316 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t), (s)))) t.FStar_Syntax_Syntax.pos)
end))


let rec force_uvar' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____347) -> begin
(

let uu____360 = (FStar_Unionfind.find uv)
in (match (uu____360) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar' t')
end
| uu____374 -> begin
t
end))
end
| uu____378 -> begin
t
end))


let force_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (

let t' = (force_uvar' t)
in (

let uu____391 = (FStar_Util.physical_equality t t')
in (match (uu____391) with
| true -> begin
t
end
| uu____396 -> begin
(delay t' (([]), (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))))
end))))


let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(

let uu____450 = (FStar_ST.read m)
in (match (uu____450) with
| FStar_Pervasives_Native.None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(

let t' = (

let uu____486 = (c ())
in (force_delayed_thunk uu____486))
in ((FStar_ST.write m (FStar_Pervasives_Native.Some (t')));
t';
))
end
| uu____497 -> begin
t
end)
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let t'1 = (force_delayed_thunk t')
in ((FStar_ST.write m (FStar_Pervasives_Native.Some (t'1)));
t'1;
))
end))
end
| uu____529 -> begin
t
end))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(

let uu____536 = (FStar_Unionfind.find u')
in (match (uu____536) with
| FStar_Pervasives_Native.Some (u1) -> begin
(compress_univ u1)
end
| uu____540 -> begin
u
end))
end
| uu____542 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___100_552 -> (match (uu___100_552) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(

let uu____556 = (

let uu____557 = (

let uu____558 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x uu____558))
in (FStar_Syntax_Syntax.bv_to_name uu____557))
in FStar_Pervasives_Native.Some (uu____556))
end
| uu____559 -> begin
FStar_Pervasives_Native.None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___101_569 -> (match (uu___101_569) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____573 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___105_574 = a
in {FStar_Syntax_Syntax.ppname = uu___105_574.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___105_574.FStar_Syntax_Syntax.sort}))
in FStar_Pervasives_Native.Some (uu____573))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____583 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___102_593 -> (match (uu___102_593) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____597 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___103_607 -> (match (uu___103_607) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____611 -> begin
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
| FStar_Syntax_Syntax.U_unif (uu____627) -> begin
u1
end
| FStar_Syntax_Syntax.U_succ (u2) -> begin
(

let uu____631 = (subst_univ s u2)
in FStar_Syntax_Syntax.U_succ (uu____631))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____634 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (uu____634))
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

let uu____667 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_bvar (uu____667))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____669 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_name (uu____669))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v1 = (

let uu___106_677 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1); FStar_Syntax_Syntax.ty = uu___106_677.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___106_677.FStar_Syntax_Syntax.p})
in (

let fv1 = (

let uu___107_693 = fv
in {FStar_Syntax_Syntax.fv_name = v1; FStar_Syntax_Syntax.fv_delta = uu___107_693.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___107_693.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv1))))
end
| t' -> begin
t'
end)
in (

let uu___108_695 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.tk = uu___108_695.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___108_695.FStar_Syntax_Syntax.vars})))
end))


let tag_lid_with_range = (fun l s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____722 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r)
in (FStar_Ident.set_lid_range l uu____722))
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
| uu____804 -> begin
(

let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_constant (uu____812) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____815) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____818) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t'), ((compose_subst s' s))))) t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (uu____899), uu____900) -> begin
(failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) (FStar_Pervasives_Native.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) (FStar_Pervasives_Native.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____956 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (

let uu____957 = (

let uu____960 = (

let uu____961 = (subst_univ (FStar_Pervasives_Native.fst s) u)
in FStar_Syntax_Syntax.Tm_type (uu____961))
in (FStar_Syntax_Syntax.mk uu____960))
in (uu____957 FStar_Pervasives_Native.None uu____956)))
end
| uu____973 -> begin
(

let uu____974 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t0), (s)))) uu____974))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___104_988 -> (match (uu___104_988) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(

let uu____992 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (uu____992))
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
| uu____1012 -> begin
(

let uu___109_1018 = t
in (

let uu____1019 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____1023 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____1026 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____1029 = (FStar_List.map (fun uu____1043 -> (match (uu____1043) with
| (t1, imp) -> begin
(

let uu____1058 = (subst' s t1)
in ((uu____1058), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (

let uu____1063 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu____1019; FStar_Syntax_Syntax.effect_name = uu____1023; FStar_Syntax_Syntax.result_typ = uu____1026; FStar_Syntax_Syntax.effect_args = uu____1029; FStar_Syntax_Syntax.flags = uu____1063}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([], FStar_Pervasives_Native.None) -> begin
t
end
| (([])::[], FStar_Pervasives_Native.None) -> begin
t
end
| uu____1085 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uopt) -> begin
(

let uu____1101 = (subst' s t1)
in (

let uu____1102 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____1101 uu____1102)))
end
| FStar_Syntax_Syntax.GTotal (t1, uopt) -> begin
(

let uu____1115 = (subst' s t1)
in (

let uu____1116 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1115 uu____1116)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1122 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp uu____1122))
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
| FStar_Syntax_Syntax.NT (uu____1137) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n1 s -> (FStar_List.map (shift n1) s))


let shift_subst' = (fun n1 s -> (

let uu____1169 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (shift_subst n1)))
in ((uu____1169), ((FStar_Pervasives_Native.snd s)))))


let subst_binder' = (fun s uu____1191 -> (match (uu____1191) with
| (x, imp) -> begin
(

let uu____1196 = (

let uu___110_1197 = x
in (

let uu____1198 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___110_1197.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___110_1197.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1198}))
in ((uu____1196), (imp)))
end))


let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((i = (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1238 -> begin
(

let uu____1239 = (shift_subst' i s)
in (subst_binder' uu____1239 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (FStar_Pervasives_Native.None)) bs))


let subst_arg' = (fun s uu____1273 -> (match (uu____1273) with
| (t, imp) -> begin
(

let uu____1284 = (subst' s t)
in ((uu____1284), (imp)))
end))


let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____1355) -> begin
((p1), (n1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1370 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1395 uu____1396 -> (match (((uu____1395), (uu____1396))) with
| ((pats1, n2), (p2, imp)) -> begin
(

let uu____1443 = (aux n2 p2)
in (match (uu____1443) with
| (p3, m) -> begin
(((((p3), (imp)))::pats1), (m))
end))
end)) (([]), (n1))))
in (match (uu____1370) with
| (pats1, n2) -> begin
(((

let uu___111_1475 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.ty = uu___111_1475.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___111_1475.FStar_Syntax_Syntax.p})), (n2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___112_1491 = x
in (

let uu____1492 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___112_1491.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___112_1491.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1492}))
in (((

let uu___113_1497 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.ty = uu___113_1497.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___113_1497.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___114_1508 = x
in (

let uu____1509 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___114_1508.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___114_1508.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1509}))
in (((

let uu___115_1514 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.ty = uu___115_1514.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___115_1514.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___116_1530 = x
in (

let uu____1531 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___116_1530.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___116_1530.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1531}))
in (

let t01 = (subst' s1 t0)
in (((

let uu___117_1539 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.ty = uu___117_1539.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___117_1539.FStar_Syntax_Syntax.p})), (n1)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| FStar_Pervasives_Native.None -> begin
lopt
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (uu____1567)) -> begin
lopt
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) -> begin
(

let uu____1573 = (

let uu____1576 = (

let uu___118_1577 = l
in (

let uu____1578 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___118_1577.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____1578; FStar_Syntax_Syntax.cflags = uu___118_1577.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____1581 -> (

let uu____1582 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s uu____1582)))}))
in FStar_Util.Inl (uu____1576))
in FStar_Pervasives_Native.Some (uu____1573))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk1 = (fun t' -> (

let uu____1605 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____1605)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1612) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_constant (uu____1635) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1638) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1643) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_type (uu____1654) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1655) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_name (uu____1656) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us1 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us)
in (

let uu____1668 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us1)
in (tag_with_range uu____1668 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(

let uu____1689 = (

let uu____1690 = (

let uu____1700 = (subst' s t0)
in (

let uu____1703 = (subst_args' s args)
in ((uu____1700), (uu____1703))))
in FStar_Syntax_Syntax.Tm_app (uu____1690))
in (mk1 uu____1689))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t1) -> begin
(

let uu____1775 = (subst' s t1)
in FStar_Util.Inl (uu____1775))
end
| FStar_Util.Inr (c) -> begin
(

let uu____1789 = (subst_comp' s c)
in FStar_Util.Inr (uu____1789))
end)
in (

let uu____1796 = (

let uu____1797 = (

let uu____1815 = (subst' s t0)
in (

let uu____1818 = (

let uu____1830 = (FStar_Util.map_opt topt (subst' s))
in ((annot1), (uu____1830)))
in ((uu____1815), (uu____1818), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____1797))
in (mk1 uu____1796)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n1 = (FStar_List.length bs)
in (

let s' = (shift_subst' n1 s)
in (

let uu____1898 = (

let uu____1899 = (

let uu____1914 = (subst_binders' s bs)
in (

let uu____1918 = (subst' s' body)
in (

let uu____1921 = (push_subst_lcomp s' lopt)
in ((uu____1914), (uu____1918), (uu____1921)))))
in FStar_Syntax_Syntax.Tm_abs (uu____1899))
in (mk1 uu____1898))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n1 = (FStar_List.length bs)
in (

let uu____1958 = (

let uu____1959 = (

let uu____1967 = (subst_binders' s bs)
in (

let uu____1971 = (

let uu____1974 = (shift_subst' n1 s)
in (subst_comp' uu____1974 comp))
in ((uu____1967), (uu____1971))))
in FStar_Syntax_Syntax.Tm_arrow (uu____1959))
in (mk1 uu____1958)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x1 = (

let uu___119_1995 = x
in (

let uu____1996 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___119_1995.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___119_1995.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1996}))
in (

let phi1 = (

let uu____2002 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____2002 phi))
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((x1), (phi1)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t01 = (subst' s t0)
in (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____2085 -> (match (uu____2085) with
| (pat, wopt, branch) -> begin
(

let uu____2121 = (subst_pat' s pat)
in (match (uu____2121) with
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

let uu____2156 = (subst' s1 w)
in FStar_Pervasives_Native.Some (uu____2156))
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

let uu____2216 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____2216) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____2219 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___120_2226 = x
in {FStar_Syntax_Syntax.ppname = uu___120_2226.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___120_2226.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((

let uu___121_2228 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___122_2229 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___122_2229.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = uu___122_2229.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___121_2228.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___121_2228.FStar_Syntax_Syntax.fv_qual}))
end)
in (

let uu___123_2244 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___123_2244.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___123_2244.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (mk1 (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs1))), (body1)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let uu____2263 = (

let uu____2264 = (

let uu____2269 = (subst' s t0)
in (

let uu____2272 = (

let uu____2273 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____2273))
in ((uu____2269), (uu____2272))))
in FStar_Syntax_Syntax.Tm_meta (uu____2264))
in (mk1 uu____2263))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) -> begin
(

let uu____2315 = (

let uu____2316 = (

let uu____2321 = (subst' s t0)
in (

let uu____2324 = (

let uu____2325 = (

let uu____2330 = (subst' s t1)
in ((m), (uu____2330)))
in FStar_Syntax_Syntax.Meta_monadic (uu____2325))
in ((uu____2321), (uu____2324))))
in FStar_Syntax_Syntax.Tm_meta (uu____2316))
in (mk1 uu____2315))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) -> begin
(

let uu____2349 = (

let uu____2350 = (

let uu____2355 = (subst' s t0)
in (

let uu____2358 = (

let uu____2359 = (

let uu____2365 = (subst' s t1)
in ((m1), (m2), (uu____2365)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____2359))
in ((uu____2355), (uu____2358))))
in FStar_Syntax_Syntax.Tm_meta (uu____2350))
in (mk1 uu____2349))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____2378 = (

let uu____2379 = (

let uu____2384 = (subst' s t1)
in ((uu____2384), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____2379))
in (mk1 uu____2378))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (force_delayed_thunk t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t2, s), memo) -> begin
(

let t' = (

let uu____2447 = (push_subst s t2)
in (compress uu____2447))
in ((FStar_Unionfind.update_in_tx memo (FStar_Pervasives_Native.Some (t')));
t';
))
end
| uu____2454 -> begin
(

let t' = (force_uvar t1)
in (match (t'.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2458) -> begin
(compress t')
end
| uu____2479 -> begin
t'
end))
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (subst' (([]), (FStar_Pervasives_Native.Some ((

let uu___124_2503 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = uu___124_2503.FStar_Range.use_range})))) t))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let closing_subst = (fun bs -> (

let uu____2531 = (FStar_List.fold_right (fun uu____2540 uu____2541 -> (match (((uu____2540), (uu____2541))) with
| ((x, uu____2556), (subst1, n1)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n1))))::subst1), ((n1 + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____2531 FStar_Pervasives_Native.fst)))


let open_binders' = (fun bs -> (

let rec aux = (fun bs1 o -> (match (bs1) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___125_2636 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____2637 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___125_2636.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___125_2636.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2637}))
in (

let o1 = (

let uu____2642 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____2642)
in (

let uu____2644 = (aux bs' o1)
in (match (uu____2644) with
| (bs'1, o2) -> begin
(((((x'), (imp)))::bs'1), (o2))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____2676 = (open_binders' bs)
in (FStar_Pervasives_Native.fst uu____2676)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____2696 = (open_binders' bs)
in (match (uu____2696) with
| (bs', opening) -> begin
(

let uu____2716 = (subst opening t)
in ((bs'), (uu____2716), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____2729 = (open_term' bs t)
in (match (uu____2729) with
| (b, t1, uu____2737) -> begin
((b), (t1))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____2746 = (open_binders' bs)
in (match (uu____2746) with
| (bs', opening) -> begin
(

let uu____2765 = (subst_comp opening t)
in ((bs'), (uu____2765)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec open_pat_aux = (fun sub1 renaming p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____2816) -> begin
((p1), (sub1), (renaming))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2835 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____2881 uu____2882 -> (match (((uu____2881), (uu____2882))) with
| ((pats1, sub2, renaming1), (p2, imp)) -> begin
(

let uu____2970 = (open_pat_aux sub2 renaming1 p2)
in (match (uu____2970) with
| (p3, sub3, renaming2) -> begin
(((((p3), (imp)))::pats1), (sub3), (renaming2))
end))
end)) (([]), (sub1), (renaming))))
in (match (uu____2835) with
| (pats1, sub2, renaming1) -> begin
(((

let uu___126_3071 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.ty = uu___126_3071.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___126_3071.FStar_Syntax_Syntax.p})), (sub2), (renaming1))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___127_3085 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____3086 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___127_3085.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___127_3085.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3086}))
in (

let sub2 = (

let uu____3091 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____3091)
in (((

let uu___128_3099 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = uu___128_3099.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___128_3099.FStar_Syntax_Syntax.p})), (sub2), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___129_3106 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____3107 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___129_3106.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___129_3106.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3107}))
in (

let sub2 = (

let uu____3112 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____3112)
in (((

let uu___130_3120 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = uu___130_3120.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___130_3120.FStar_Syntax_Syntax.p})), (sub2), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___131_3132 = x
in (

let uu____3133 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___131_3132.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_3132.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3133}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___132_3143 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.ty = uu___132_3143.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___132_3143.FStar_Syntax_Syntax.p})), (sub1), (renaming))))
end))
in (

let uu____3146 = (open_pat_aux [] [] p)
in (match (uu____3146) with
| (p1, sub1, uu____3162) -> begin
((p1), (sub1))
end))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____3180 -> (match (uu____3180) with
| (p, wopt, e) -> begin
(

let uu____3198 = (open_pat p)
in (match (uu____3198) with
| (p1, opening) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____3213 = (subst opening w)
in FStar_Pervasives_Native.Some (uu____3213))
end)
in (

let e1 = (subst opening e)
in ((p1), (wopt1), (e1))))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____3222 = (closing_subst bs)
in (subst uu____3222 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____3230 = (closing_subst bs)
in (subst_comp uu____3230 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs1 -> (match (bs1) with
| [] -> begin
[]
end
| ((x, imp))::tl1 -> begin
(

let x1 = (

let uu___133_3263 = x
in (

let uu____3264 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___133_3263.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_3263.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3264}))
in (

let s' = (

let uu____3269 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____3269)
in (

let uu____3271 = (aux s' tl1)
in (((x1), (imp)))::uu____3271)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let uu___134_3285 = lc
in (

let uu____3286 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___134_3285.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____3286; FStar_Syntax_Syntax.cflags = uu___134_3285.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____3289 -> (

let uu____3290 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s uu____3290)))}))))


let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____3326) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3342 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____3376 uu____3377 -> (match (((uu____3376), (uu____3377))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____3442 = (aux sub2 p2)
in (match (uu____3442) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____3342) with
| (pats1, sub2) -> begin
(((

let uu___135_3508 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.ty = uu___135_3508.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___135_3508.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___136_3522 = x
in (

let uu____3523 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___136_3522.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___136_3522.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3523}))
in (

let sub2 = (

let uu____3528 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____3528)
in (((

let uu___137_3533 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.ty = uu___137_3533.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___137_3533.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___138_3538 = x
in (

let uu____3539 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___138_3538.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___138_3538.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3539}))
in (

let sub2 = (

let uu____3544 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____3544)
in (((

let uu___139_3549 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.ty = uu___139_3549.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___139_3549.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___140_3559 = x
in (

let uu____3560 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___140_3559.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___140_3559.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3560}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___141_3567 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.ty = uu___141_3567.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___141_3567.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____3572 -> (match (uu____3572) with
| (p, wopt, e) -> begin
(

let uu____3590 = (close_pat p)
in (match (uu____3590) with
| (p1, closing) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____3614 = (subst closing w)
in FStar_Pervasives_Native.Some (uu____3614))
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


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (

let uu____3646 = (univ_var_opening us)
in (match (uu____3646) with
| (s, us') -> begin
(

let t1 = (subst s t)
in ((us'), (t1)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____3671 = (univ_var_opening us)
in (match (uu____3671) with
| (s, us') -> begin
(

let uu____3684 = (subst_comp s c)
in ((us'), (uu____3684)))
end)))


let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun us t -> (

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD (((u), ((n1 - i)))))))
in (subst s t))))


let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun us c -> (

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD (((u), ((n1 - i)))))))
in (subst_comp s c))))


let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____3727 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____3727) with
| true -> begin
((lbs), (t))
end
| uu____3732 -> begin
(

let uu____3733 = (FStar_List.fold_right (fun lb uu____3745 -> (match (uu____3745) with
| (i, lbs1, out) -> begin
(

let x = (

let uu____3764 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____3764))
in (((i + (Prims.parse_int "1"))), (((

let uu___142_3767 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___142_3767.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___142_3767.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___142_3767.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___142_3767.FStar_Syntax_Syntax.lbdef}))::lbs1), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
in (match (uu____3733) with
| (n_let_recs, lbs1, let_rec_opening) -> begin
(

let lbs2 = (FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let uu____3785 = (FStar_List.fold_right (fun u uu____3797 -> (match (uu____3797) with
| (i, us, out) -> begin
(((i + (Prims.parse_int "1"))), ((u)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u)))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____3785) with
| (uu____3819, us, u_let_rec_opening) -> begin
(

let uu___143_3826 = lb
in (

let uu____3827 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___143_3826.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu___143_3826.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___143_3826.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____3827}))
end)))))
in (

let t1 = (subst let_rec_opening t)
in ((lbs2), (t1))))
end))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____3843 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____3843) with
| true -> begin
((lbs), (t))
end
| uu____3848 -> begin
(

let uu____3849 = (FStar_List.fold_right (fun lb uu____3857 -> (match (uu____3857) with
| (i, out) -> begin
(

let uu____3868 = (

let uu____3870 = (

let uu____3871 = (

let uu____3874 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____3874), (i)))
in FStar_Syntax_Syntax.NM (uu____3871))
in (uu____3870)::out)
in (((i + (Prims.parse_int "1"))), (uu____3868)))
end)) lbs (((Prims.parse_int "0")), ([])))
in (match (uu____3849) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____3889 = (FStar_List.fold_right (fun u uu____3897 -> (match (uu____3897) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____3889) with
| (uu____3910, u_let_rec_closing) -> begin
(

let uu___144_3914 = lb
in (

let uu____3915 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___144_3914.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___144_3914.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___144_3914.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___144_3914.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____3915}))
end)))))
in (

let t1 = (subst let_rec_closing t)
in ((lbs1), (t1))))
end))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____3925 -> (match (uu____3925) with
| (us, t) -> begin
(

let n1 = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____3943 -> (match (uu____3943) with
| (x, uu____3947) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n1 - i)))))
end)) binders)
in (

let t1 = (subst s t)
in ((us), (t1))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____3958 -> (match (uu____3958) with
| (us', t) -> begin
(

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n1 - i)))))) us)
in (

let uu____3976 = (subst s t)
in ((us'), (uu____3976))))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n1 = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____3991 -> (match (uu____3991) with
| (x, uu____3995) -> begin
FStar_Syntax_Syntax.DB ((((n1 - i)), (x)))
end))))))




