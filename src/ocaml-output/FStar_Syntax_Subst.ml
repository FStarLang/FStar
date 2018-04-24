
open Prims
open FStar_Pervasives

let subst_to_string : 'Auu____5 . (FStar_Syntax_Syntax.bv * 'Auu____5) Prims.list  ->  Prims.string = (fun s -> (

let uu____23 = (FStar_All.pipe_right s (FStar_List.map (fun uu____41 -> (match (uu____41) with
| (b, uu____47) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right uu____23 (FStar_String.concat ", "))))


let rec apply_until_some : 'Auu____60 'Auu____61 . ('Auu____60  ->  'Auu____61 FStar_Pervasives_Native.option)  ->  'Auu____60 Prims.list  ->  ('Auu____60 Prims.list * 'Auu____61) FStar_Pervasives_Native.option = (fun f s -> (match (s) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (s0)::rest -> begin
(

let uu____103 = (f s0)
in (match (uu____103) with
| FStar_Pervasives_Native.None -> begin
(apply_until_some f rest)
end
| FStar_Pervasives_Native.Some (st) -> begin
FStar_Pervasives_Native.Some (((rest), (st)))
end))
end))


let map_some_curry : 'Auu____135 'Auu____136 'Auu____137 . ('Auu____135  ->  'Auu____136  ->  'Auu____137)  ->  'Auu____137  ->  ('Auu____135 * 'Auu____136) FStar_Pervasives_Native.option  ->  'Auu____137 = (fun f x uu___39_164 -> (match (uu___39_164) with
| FStar_Pervasives_Native.None -> begin
x
end
| FStar_Pervasives_Native.Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map : 'Auu____199 'Auu____200 'Auu____201 . ('Auu____199  ->  'Auu____200 FStar_Pervasives_Native.option)  ->  'Auu____199 Prims.list  ->  ('Auu____199 Prims.list  ->  'Auu____200  ->  'Auu____201)  ->  'Auu____201  ->  'Auu____201 = (fun f s g t -> (

let uu____249 = (apply_until_some f s)
in (FStar_All.pipe_right uu____249 (map_some_curry g t))))


let compose_subst : 'Auu____276 'Auu____277 . ('Auu____276 Prims.list * 'Auu____277 FStar_Pervasives_Native.option)  ->  ('Auu____276 Prims.list * 'Auu____277 FStar_Pervasives_Native.option)  ->  ('Auu____276 Prims.list * 'Auu____277 FStar_Pervasives_Native.option) = (fun s1 s2 -> (

let s = (FStar_List.append (FStar_Pervasives_Native.fst s1) (FStar_Pervasives_Native.fst s2))
in (

let ropt = (match ((FStar_Pervasives_Native.snd s2)) with
| FStar_Pervasives_Native.Some (uu____348) -> begin
(FStar_Pervasives_Native.snd s2)
end
| uu____353 -> begin
(FStar_Pervasives_Native.snd s1)
end)
in ((s), (ropt)))))


let delay : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term = (fun t s -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t'), ((compose_subst s' s))) t.FStar_Syntax_Syntax.pos)
end
| uu____463 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t), (s)) t.FStar_Syntax_Syntax.pos)
end))


let rec force_uvar' : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____498) -> begin
(

let uu____523 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____523) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____533 = (

let uu____536 = (force_uvar' t')
in (FStar_Pervasives_Native.fst uu____536))
in ((uu____533), (true)))
end
| uu____547 -> begin
((t), (false))
end))
end
| uu____552 -> begin
((t), (false))
end))


let force_uvar : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (

let uu____570 = (force_uvar' t)
in (match (uu____570) with
| (t', forced) -> begin
(match ((not (forced))) with
| true -> begin
((t), (forced))
end
| uu____597 -> begin
(

let uu____598 = (delay t' (([]), (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))))
in ((uu____598), (forced)))
end)
end)))


let rec try_read_memo_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(

let uu____670 = (FStar_ST.op_Bang m)
in (match (uu____670) with
| FStar_Pervasives_Native.None -> begin
((t), (false))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____797 = (try_read_memo_aux t')
in (match (uu____797) with
| (t'1, shorten) -> begin
((match (shorten) with
| true -> begin
(FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some (t'1)))
end
| uu____926 -> begin
()
end);
((t'1), (true));
)
end))
end))
end
| uu____929 -> begin
((t), (false))
end))


let try_read_memo : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____943 = (try_read_memo_aux t)
in (FStar_Pervasives_Native.fst uu____943)))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(

let uu____966 = (FStar_Syntax_Unionfind.univ_find u')
in (match (uu____966) with
| FStar_Pervasives_Native.Some (u1) -> begin
(compress_univ u1)
end
| uu____970 -> begin
u
end))
end
| uu____973 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___40_994 -> (match (uu___40_994) with
| FStar_Syntax_Syntax.DB (i, x) when (Prims.op_Equality i a.FStar_Syntax_Syntax.index) -> begin
(

let uu____999 = (

let uu____1000 = (

let uu____1001 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x uu____1001))
in (FStar_Syntax_Syntax.bv_to_name uu____1000))
in FStar_Pervasives_Native.Some (uu____999))
end
| uu____1002 -> begin
FStar_Pervasives_Native.None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___41_1023 -> (match (uu___41_1023) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____1028 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___45_1031 = a
in {FStar_Syntax_Syntax.ppname = uu___45_1031.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___45_1031.FStar_Syntax_Syntax.sort}))
in FStar_Pervasives_Native.Some (uu____1028))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____1040 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___42_1060 -> (match (uu___42_1060) with
| FStar_Syntax_Syntax.UN (y, t) when (Prims.op_Equality x y) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____1065 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___43_1085 -> (match (uu___43_1085) with
| FStar_Syntax_Syntax.UD (y, i) when (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____1090 -> begin
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
| FStar_Syntax_Syntax.U_unif (uu____1116) -> begin
u1
end
| FStar_Syntax_Syntax.U_succ (u2) -> begin
(

let uu____1126 = (subst_univ s u2)
in FStar_Syntax_Syntax.U_succ (uu____1126))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1130 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (uu____1130))
end)))


let tag_with_range : 'Auu____1139 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ('Auu____1139 * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
t
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let r1 = (

let uu____1172 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1172))
in (

let t' = (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____1175 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_bvar (uu____1175))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____1177 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_name (uu____1177))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v1 = (

let uu___46_1183 = fv.FStar_Syntax_Syntax.fv_name
in (

let uu____1184 = (FStar_Ident.set_lid_range l r1)
in {FStar_Syntax_Syntax.v = uu____1184; FStar_Syntax_Syntax.p = uu___46_1183.FStar_Syntax_Syntax.p}))
in (

let fv1 = (

let uu___47_1186 = fv
in {FStar_Syntax_Syntax.fv_name = v1; FStar_Syntax_Syntax.fv_delta = uu___47_1186.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___47_1186.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv1))))
end
| t' -> begin
t'
end)
in (

let uu___48_1188 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___48_1188.FStar_Syntax_Syntax.vars})))
end))


let tag_lid_with_range : 'Auu____1197 . FStar_Ident.lident  ->  ('Auu____1197 * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Ident.lident = (fun l s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____1223 = (

let uu____1224 = (FStar_Ident.range_of_lid l)
in (

let uu____1225 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range uu____1224 uu____1225)))
in (FStar_Ident.set_lid_range l uu____1223))
end))


let mk_range : FStar_Range.range  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Range.range = (fun r s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
r
end
| FStar_Pervasives_Native.Some (r') -> begin
(

let uu____1243 = (FStar_Range.use_range r')
in (FStar_Range.set_use_range r uu____1243))
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
| uu____1367 -> begin
(

let t0 = (try_read_memo t)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1377) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1382) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1387) -> begin
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

let uu____1496 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (

let uu____1497 = (

let uu____1504 = (

let uu____1505 = (subst_univ (FStar_Pervasives_Native.fst s) u)
in FStar_Syntax_Syntax.Tm_type (uu____1505))
in (FStar_Syntax_Syntax.mk uu____1504))
in (uu____1497 FStar_Pervasives_Native.None uu____1496)))
end
| uu____1515 -> begin
(

let uu____1516 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed ((t0), (s)) uu____1516))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___44_1530 -> (match (uu___44_1530) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(

let uu____1534 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (uu____1534))
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
| uu____1568 -> begin
(

let uu___49_1579 = t
in (

let uu____1580 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____1587 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____1592 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____1595 = (FStar_List.map (fun uu____1620 -> (match (uu____1620) with
| (t1, imp) -> begin
(

let uu____1639 = (subst' s t1)
in ((uu____1639), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (

let uu____1644 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu____1580; FStar_Syntax_Syntax.effect_name = uu____1587; FStar_Syntax_Syntax.result_typ = uu____1592; FStar_Syntax_Syntax.effect_args = uu____1595; FStar_Syntax_Syntax.flags = uu____1644}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([], FStar_Pervasives_Native.None) -> begin
t
end
| (([])::[], FStar_Pervasives_Native.None) -> begin
t
end
| uu____1681 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uopt) -> begin
(

let uu____1704 = (subst' s t1)
in (

let uu____1705 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____1704 uu____1705)))
end
| FStar_Syntax_Syntax.GTotal (t1, uopt) -> begin
(

let uu____1724 = (subst' s t1)
in (

let uu____1725 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1724 uu____1725)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1735 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp uu____1735))
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
| FStar_Syntax_Syntax.NT (uu____1754) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n1 s -> (FStar_List.map (shift n1) s))


let shift_subst' : 'Auu____1777 . Prims.int  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1777)  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1777) = (fun n1 s -> (

let uu____1806 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (shift_subst n1)))
in ((uu____1806), ((FStar_Pervasives_Native.snd s)))))


let subst_binder' : 'Auu____1825 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.bv * 'Auu____1825)  ->  (FStar_Syntax_Syntax.bv * 'Auu____1825) = (fun s uu____1843 -> (match (uu____1843) with
| (x, imp) -> begin
(

let uu____1850 = (

let uu___50_1851 = x
in (

let uu____1852 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___50_1851.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___50_1851.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1852}))
in ((uu____1850), (imp)))
end))


let subst_binders' : 'Auu____1861 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.bv * 'Auu____1861) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____1861) Prims.list = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1922 -> begin
(

let uu____1923 = (shift_subst' i s)
in (subst_binder' uu____1923 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (FStar_Pervasives_Native.None)) bs))


let subst_arg' : 'Auu____1956 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1956)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1956) = (fun s uu____1978 -> (match (uu____1978) with
| (t, imp) -> begin
(

let uu____1991 = (subst' s t)
in ((uu____1991), (imp)))
end))


let subst_args' : 'Auu____2001 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____2001) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____2001) Prims.list = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____2100) -> begin
((p1), (n1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2121 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____2175 uu____2176 -> (match (((uu____2175), (uu____2176))) with
| ((pats1, n2), (p2, imp)) -> begin
(

let uu____2255 = (aux n2 p2)
in (match (uu____2255) with
| (p3, m) -> begin
(((((p3), (imp)))::pats1), (m))
end))
end)) (([]), (n1))))
in (match (uu____2121) with
| (pats1, n2) -> begin
(((

let uu___51_2313 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___51_2313.FStar_Syntax_Syntax.p})), (n2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___52_2339 = x
in (

let uu____2340 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___52_2339.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___52_2339.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2340}))
in (((

let uu___53_2346 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___53_2346.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___54_2362 = x
in (

let uu____2363 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___54_2362.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___54_2362.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2363}))
in (((

let uu___55_2369 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___55_2369.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___56_2390 = x
in (

let uu____2391 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___56_2390.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___56_2390.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2391}))
in (

let t01 = (subst' s1 t0)
in (((

let uu___57_2400 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___57_2400.FStar_Syntax_Syntax.p})), (n1)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s lopt -> (match (lopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____2424 = (

let uu___58_2425 = rc
in (

let uu____2426 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (subst' s))
in {FStar_Syntax_Syntax.residual_effect = uu___58_2425.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____2426; FStar_Syntax_Syntax.residual_flags = uu___58_2425.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____2424))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk1 = (fun t' -> (

let uu____2459 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2459)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2462) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
t
end
| FStar_Syntax_Syntax.Tm_constant (uu____2490) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2495) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2500) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_type (uu____2525) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2526) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_name (uu____2527) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us1 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us)
in (

let uu____2543 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us1)
in (tag_with_range uu____2543 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(

let uu____2572 = (

let uu____2573 = (

let uu____2588 = (subst' s t0)
in (

let uu____2591 = (subst_args' s args)
in ((uu____2588), (uu____2591))))
in FStar_Syntax_Syntax.Tm_app (uu____2573))
in (mk1 uu____2572))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t1) -> begin
(

let uu____2686 = (subst' s t1)
in FStar_Util.Inl (uu____2686))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2700 = (subst_comp' s c)
in FStar_Util.Inr (uu____2700))
end)
in (

let uu____2707 = (

let uu____2708 = (

let uu____2735 = (subst' s t0)
in (

let uu____2738 = (

let uu____2755 = (FStar_Util.map_opt topt (subst' s))
in ((annot1), (uu____2755)))
in ((uu____2735), (uu____2738), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2708))
in (mk1 uu____2707)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n1 = (FStar_List.length bs)
in (

let s' = (shift_subst' n1 s)
in (

let uu____2839 = (

let uu____2840 = (

let uu____2857 = (subst_binders' s bs)
in (

let uu____2864 = (subst' s' body)
in (

let uu____2867 = (push_subst_lcomp s' lopt)
in ((uu____2857), (uu____2864), (uu____2867)))))
in FStar_Syntax_Syntax.Tm_abs (uu____2840))
in (mk1 uu____2839))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n1 = (FStar_List.length bs)
in (

let uu____2903 = (

let uu____2904 = (

let uu____2917 = (subst_binders' s bs)
in (

let uu____2924 = (

let uu____2927 = (shift_subst' n1 s)
in (subst_comp' uu____2927 comp))
in ((uu____2917), (uu____2924))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2904))
in (mk1 uu____2903)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x1 = (

let uu___59_2959 = x
in (

let uu____2960 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___59_2959.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___59_2959.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2960}))
in (

let phi1 = (

let uu____2966 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____2966 phi))
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((x1), (phi1)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t01 = (subst' s t0)
in (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____3093 -> (match (uu____3093) with
| (pat, wopt, branch) -> begin
(

let uu____3139 = (subst_pat' s pat)
in (match (uu____3139) with
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

let uu____3187 = (subst' s1 w)
in FStar_Pervasives_Native.Some (uu____3187))
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

let uu____3272 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____3272) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____3275 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___60_3287 = x
in {FStar_Syntax_Syntax.ppname = uu___60_3287.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___60_3287.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr (fv)
end)
in (

let uu___61_3289 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___61_3289.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___61_3289.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd; FStar_Syntax_Syntax.lbattrs = uu___61_3289.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___61_3289.FStar_Syntax_Syntax.lbpos})))))))
in (mk1 (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs1))), (body1)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let uu____3316 = (

let uu____3317 = (

let uu____3324 = (subst' s t0)
in (

let uu____3327 = (

let uu____3328 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____3328))
in ((uu____3324), (uu____3327))))
in FStar_Syntax_Syntax.Tm_meta (uu____3317))
in (mk1 uu____3316))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) -> begin
(

let uu____3388 = (

let uu____3389 = (

let uu____3396 = (subst' s t0)
in (

let uu____3399 = (

let uu____3400 = (

let uu____3407 = (subst' s t1)
in ((m), (uu____3407)))
in FStar_Syntax_Syntax.Meta_monadic (uu____3400))
in ((uu____3396), (uu____3399))))
in FStar_Syntax_Syntax.Tm_meta (uu____3389))
in (mk1 uu____3388))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) -> begin
(

let uu____3426 = (

let uu____3427 = (

let uu____3434 = (subst' s t0)
in (

let uu____3437 = (

let uu____3438 = (

let uu____3447 = (subst' s t1)
in ((m1), (m2), (uu____3447)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____3438))
in ((uu____3434), (uu____3437))))
in FStar_Syntax_Syntax.Tm_meta (uu____3427))
in (mk1 uu____3426))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____3462 = (

let uu____3463 = (

let uu____3470 = (subst' s tm)
in ((uu____3470), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____3463))
in (mk1 uu____3462))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted (subst' s) qi)
in (mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi1))))))
end)
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____3484 = (

let uu____3485 = (

let uu____3492 = (subst' s t1)
in ((uu____3492), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____3485))
in (mk1 uu____3484))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (try_read_memo t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s), memo) -> begin
((

let uu____3557 = (

let uu____3562 = (push_subst s t')
in FStar_Pervasives_Native.Some (uu____3562))
in (FStar_ST.op_Colon_Equals memo uu____3557));
(compress t1);
)
end
| uu____3674 -> begin
(

let uu____3675 = (force_uvar t1)
in (match (uu____3675) with
| (t', forced) -> begin
(match (t'.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____3688) -> begin
(compress t')
end
| uu____3713 -> begin
t'
end)
end))
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (

let uu____3748 = (

let uu____3749 = (

let uu____3752 = (

let uu____3753 = (FStar_Range.use_range r)
in (FStar_Range.set_def_range r uu____3753))
in FStar_Pervasives_Native.Some (uu____3752))
in (([]), (uu____3749)))
in (subst' uu____3748 t)))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let closing_subst : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun bs -> (

let uu____3793 = (FStar_List.fold_right (fun uu____3816 uu____3817 -> (match (((uu____3816), (uu____3817))) with
| ((x, uu____3845), (subst1, n1)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n1))))::subst1), ((n1 + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____3793 FStar_Pervasives_Native.fst)))


let open_binders' : 'Auu____3880 . (FStar_Syntax_Syntax.bv * 'Auu____3880) Prims.list  ->  ((FStar_Syntax_Syntax.bv * 'Auu____3880) Prims.list * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun bs -> (

let rec aux = (fun bs1 o -> (match (bs1) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___62_3991 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____3992 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___62_3991.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___62_3991.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3992}))
in (

let o1 = (

let uu____3998 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____3998)
in (

let uu____4001 = (aux bs' o1)
in (match (uu____4001) with
| (bs'1, o2) -> begin
(((((x'), (imp)))::bs'1), (o2))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____4061 = (open_binders' bs)
in (FStar_Pervasives_Native.fst uu____4061)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____4098 = (open_binders' bs)
in (match (uu____4098) with
| (bs', opening) -> begin
(

let uu____4135 = (subst opening t)
in ((bs'), (uu____4135), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____4158 = (open_term' bs t)
in (match (uu____4158) with
| (b, t1, uu____4171) -> begin
((b), (t1))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____4186 = (open_binders' bs)
in (match (uu____4186) with
| (bs', opening) -> begin
(

let uu____4221 = (subst_comp opening t)
in ((bs'), (uu____4221)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec open_pat_aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4276) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4299 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4365 uu____4366 -> (match (((uu____4365), (uu____4366))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____4469 = (open_pat_aux sub2 p2)
in (match (uu____4469) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4299) with
| (pats1, sub2) -> begin
(((

let uu___63_4571 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___63_4571.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___64_4590 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4591 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___64_4590.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___64_4590.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4591}))
in (

let sub2 = (

let uu____4597 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4597)
in (((

let uu___65_4605 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.p = uu___65_4605.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___66_4610 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4611 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___66_4610.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___66_4610.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4611}))
in (

let sub2 = (

let uu____4617 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4617)
in (((

let uu___67_4625 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.p = uu___67_4625.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___68_4635 = x
in (

let uu____4636 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___68_4635.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___68_4635.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4636}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___69_4645 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___69_4645.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (open_pat_aux [] p)))


let open_branch' : FStar_Syntax_Syntax.branch  ->  (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t) = (fun uu____4656 -> (match (uu____4656) with
| (p, wopt, e) -> begin
(

let uu____4680 = (open_pat p)
in (match (uu____4680) with
| (p1, opening) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____4703 = (subst opening w)
in FStar_Pervasives_Native.Some (uu____4703))
end)
in (

let e1 = (subst opening e)
in ((((p1), (wopt1), (e1))), (opening))))
end))
end))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun br -> (

let uu____4720 = (open_branch' br)
in (match (uu____4720) with
| (br1, uu____4726) -> begin
br1
end)))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____4737 = (closing_subst bs)
in (subst uu____4737 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____4750 = (closing_subst bs)
in (subst_comp uu____4750 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs1 -> (match (bs1) with
| [] -> begin
[]
end
| ((x, imp))::tl1 -> begin
(

let x1 = (

let uu___70_4807 = x
in (

let uu____4808 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___70_4807.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___70_4807.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4808}))
in (

let s' = (

let uu____4814 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____4814)
in (

let uu____4817 = (aux s' tl1)
in (((x1), (imp)))::uu____4817)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____4843 -> (

let uu____4844 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (subst_comp s uu____4844))))))


let close_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4897) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4920 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4986 uu____4987 -> (match (((uu____4986), (uu____4987))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____5090 = (aux sub2 p2)
in (match (uu____5090) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4920) with
| (pats1, sub2) -> begin
(((

let uu___71_5192 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___71_5192.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___72_5211 = x
in (

let uu____5212 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___72_5211.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___72_5211.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5212}))
in (

let sub2 = (

let uu____5218 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5218)
in (((

let uu___73_5226 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___73_5226.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___74_5231 = x
in (

let uu____5232 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___74_5231.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___74_5231.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5232}))
in (

let sub2 = (

let uu____5238 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5238)
in (((

let uu___75_5246 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___75_5246.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___76_5256 = x
in (

let uu____5257 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___76_5256.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___76_5256.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5257}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___77_5266 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___77_5266.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____5273 -> (match (uu____5273) with
| (p, wopt, e) -> begin
(

let uu____5293 = (close_pat p)
in (match (uu____5293) with
| (p1, closing) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____5324 = (subst closing w)
in FStar_Pervasives_Native.Some (uu____5324))
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

let uu____5387 = (univ_var_opening us)
in (match (uu____5387) with
| (s, us') -> begin
(

let t1 = (subst s t)
in ((us'), (t1)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____5431 = (univ_var_opening us)
in (match (uu____5431) with
| (s, us') -> begin
(

let uu____5454 = (subst_comp s c)
in ((us'), (uu____5454)))
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

let uu____5510 = (

let uu____5521 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5521) with
| true -> begin
(((Prims.parse_int "0")), (lbs), ([]))
end
| uu____5536 -> begin
(FStar_List.fold_right (fun lb uu____5554 -> (match (uu____5554) with
| (i, lbs1, out) -> begin
(

let x = (

let uu____5587 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____5587))
in (((i + (Prims.parse_int "1"))), (((

let uu___78_5593 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___78_5593.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___78_5593.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___78_5593.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___78_5593.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___78_5593.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___78_5593.FStar_Syntax_Syntax.lbpos}))::lbs1), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
end))
in (match (uu____5510) with
| (n_let_recs, lbs1, let_rec_opening) -> begin
(

let lbs2 = (FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let uu____5631 = (FStar_List.fold_right (fun u uu____5659 -> (match (uu____5659) with
| (i, us, out) -> begin
(

let u1 = (FStar_Syntax_Syntax.new_univ_name FStar_Pervasives_Native.None)
in (((i + (Prims.parse_int "1"))), ((u1)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u1)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____5631) with
| (uu____5700, us, u_let_rec_opening) -> begin
(

let uu___79_5711 = lb
in (

let uu____5712 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____5715 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___79_5711.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu____5712; FStar_Syntax_Syntax.lbeff = uu___79_5711.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5715; FStar_Syntax_Syntax.lbattrs = uu___79_5711.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___79_5711.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_opening t)
in ((lbs2), (t1))))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____5741 = (

let uu____5748 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5748) with
| true -> begin
(((Prims.parse_int "0")), ([]))
end
| uu____5757 -> begin
(FStar_List.fold_right (fun lb uu____5770 -> (match (uu____5770) with
| (i, out) -> begin
(

let uu____5789 = (

let uu____5792 = (

let uu____5793 = (

let uu____5798 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____5798), (i)))
in FStar_Syntax_Syntax.NM (uu____5793))
in (uu____5792)::out)
in (((i + (Prims.parse_int "1"))), (uu____5789)))
end)) lbs (((Prims.parse_int "0")), ([])))
end))
in (match (uu____5741) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____5830 = (FStar_List.fold_right (fun u uu____5848 -> (match (uu____5848) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____5830) with
| (uu____5871, u_let_rec_closing) -> begin
(

let uu___80_5877 = lb
in (

let uu____5878 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____5881 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___80_5877.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___80_5877.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____5878; FStar_Syntax_Syntax.lbeff = uu___80_5877.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5881; FStar_Syntax_Syntax.lbattrs = uu___80_5877.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___80_5877.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_closing t)
in ((lbs1), (t1))))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____5896 -> (match (uu____5896) with
| (us, t) -> begin
(

let n1 = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____5921 -> (match (uu____5921) with
| (x, uu____5927) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n1 - i)))))
end)) binders)
in (

let t1 = (subst s t)
in ((us), (t1))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____5946 -> (match (uu____5946) with
| (us', t) -> begin
(

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n1 - i)))))) us)
in (

let uu____5968 = (subst s t)
in ((us'), (uu____5968))))))
end))


let subst_tscheme : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun s uu____5982 -> (match (uu____5982) with
| (us, t) -> begin
(

let s1 = (shift_subst (FStar_List.length us) s)
in (

let uu____5992 = (subst s1 t)
in ((us), (uu____5992))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n1 = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____6016 -> (match (uu____6016) with
| (x, uu____6022) -> begin
FStar_Syntax_Syntax.DB ((((n1 - i)), (x)))
end))))))


let closing_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (closing_subst bs))


let open_term_1 : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term) = (fun b t -> (

let uu____6042 = (open_term ((b)::[]) t)
in (match (uu____6042) with
| ((b1)::[], t1) -> begin
((b1), (t1))
end
| uu____6075 -> begin
(failwith "impossible: open_term_1")
end)))


let open_term_bvs : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun bvs t -> (

let uu____6104 = (

let uu____6109 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (open_term uu____6109 t))
in (match (uu____6104) with
| (bs, t1) -> begin
(

let uu____6118 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in ((uu____6118), (t1)))
end)))


let open_term_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun bv t -> (

let uu____6141 = (open_term_bvs ((bv)::[]) t)
in (match (uu____6141) with
| ((bv1)::[], t1) -> begin
((bv1), (t1))
end
| uu____6156 -> begin
(failwith "impossible: open_term_bv")
end)))




