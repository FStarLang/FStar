
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


let map_some_curry : 'Auu____135 'Auu____136 'Auu____137 . ('Auu____135  ->  'Auu____136  ->  'Auu____137)  ->  'Auu____137  ->  ('Auu____135 * 'Auu____136) FStar_Pervasives_Native.option  ->  'Auu____137 = (fun f x uu___36_164 -> (match (uu___36_164) with
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
| uu____451 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t), (s)) t.FStar_Syntax_Syntax.pos)
end))


let rec force_uvar' : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar ({FStar_Syntax_Syntax.ctx_uvar_head = uv; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____474; FStar_Syntax_Syntax.ctx_uvar_binders = uu____475; FStar_Syntax_Syntax.ctx_uvar_typ = uu____476; FStar_Syntax_Syntax.ctx_uvar_reason = uu____477; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____478; FStar_Syntax_Syntax.ctx_uvar_range = uu____479}) -> begin
(

let uu____500 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____500) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____510 = (

let uu____513 = (force_uvar' t')
in (FStar_Pervasives_Native.fst uu____513))
in ((uu____510), (true)))
end
| uu____524 -> begin
((t), (false))
end))
end
| uu____529 -> begin
((t), (false))
end))


let force_uvar : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term * Prims.bool) = (fun t -> (

let uu____545 = (force_uvar' t)
in (match (uu____545) with
| (t', forced) -> begin
(match ((not (forced))) with
| true -> begin
((t), (forced))
end
| uu____566 -> begin
(

let uu____567 = (delay t' (([]), (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))))
in ((uu____567), (forced)))
end)
end)))


let rec try_read_memo_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(

let uu____639 = (FStar_ST.op_Bang m)
in (match (uu____639) with
| FStar_Pervasives_Native.None -> begin
((t), (false))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____712 = (try_read_memo_aux t')
in (match (uu____712) with
| (t'1, shorten) -> begin
((match (shorten) with
| true -> begin
(FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some (t'1)))
end
| uu____787 -> begin
()
end);
((t'1), (true));
)
end))
end))
end
| uu____790 -> begin
((t), (false))
end))


let try_read_memo : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____804 = (try_read_memo_aux t)
in (FStar_Pervasives_Native.fst uu____804)))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(

let uu____827 = (FStar_Syntax_Unionfind.univ_find u')
in (match (uu____827) with
| FStar_Pervasives_Native.Some (u1) -> begin
(compress_univ u1)
end
| uu____831 -> begin
u
end))
end
| uu____834 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___37_855 -> (match (uu___37_855) with
| FStar_Syntax_Syntax.DB (i, x) when (Prims.op_Equality i a.FStar_Syntax_Syntax.index) -> begin
(

let uu____860 = (

let uu____861 = (

let uu____862 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x uu____862))
in (FStar_Syntax_Syntax.bv_to_name uu____861))
in FStar_Pervasives_Native.Some (uu____860))
end
| uu____863 -> begin
FStar_Pervasives_Native.None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___38_888 -> (match (uu___38_888) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____895 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___42_900 = a
in {FStar_Syntax_Syntax.ppname = uu___42_900.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___42_900.FStar_Syntax_Syntax.sort}))
in FStar_Pervasives_Native.Some (uu____895))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____911 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___39_933 -> (match (uu___39_933) with
| FStar_Syntax_Syntax.UN (y, t) when (Prims.op_Equality x y) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____938 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___40_958 -> (match (uu___40_958) with
| FStar_Syntax_Syntax.UD (y, i) when (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____963 -> begin
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
| FStar_Syntax_Syntax.U_unif (uu____989) -> begin
u1
end
| FStar_Syntax_Syntax.U_succ (u2) -> begin
(

let uu____999 = (subst_univ s u2)
in FStar_Syntax_Syntax.U_succ (uu____999))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1003 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (uu____1003))
end)))


let tag_with_range : 'Auu____1012 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ('Auu____1012 * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
t
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let r1 = (

let uu____1045 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1045))
in (

let t' = (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____1048 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_bvar (uu____1048))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____1050 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_name (uu____1050))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v1 = (

let uu___43_1056 = fv.FStar_Syntax_Syntax.fv_name
in (

let uu____1057 = (FStar_Ident.set_lid_range l r1)
in {FStar_Syntax_Syntax.v = uu____1057; FStar_Syntax_Syntax.p = uu___43_1056.FStar_Syntax_Syntax.p}))
in (

let fv1 = (

let uu___44_1059 = fv
in {FStar_Syntax_Syntax.fv_name = v1; FStar_Syntax_Syntax.fv_delta = uu___44_1059.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___44_1059.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv1))))
end
| t' -> begin
t'
end)
in (

let uu___45_1061 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___45_1061.FStar_Syntax_Syntax.vars})))
end))


let tag_lid_with_range : 'Auu____1070 . FStar_Ident.lident  ->  ('Auu____1070 * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Ident.lident = (fun l s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____1096 = (

let uu____1097 = (FStar_Ident.range_of_lid l)
in (

let uu____1098 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range uu____1097 uu____1098)))
in (FStar_Ident.set_lid_range l uu____1096))
end))


let mk_range : FStar_Range.range  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Range.range = (fun r s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
r
end
| FStar_Pervasives_Native.Some (r') -> begin
(

let uu____1116 = (FStar_Range.use_range r')
in (FStar_Range.set_use_range r uu____1116))
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
| uu____1238 -> begin
(

let t0 = (try_read_memo t)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1248) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1253) -> begin
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

let uu____1336 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (

let uu____1337 = (

let uu____1344 = (

let uu____1345 = (subst_univ (FStar_Pervasives_Native.fst s) u)
in FStar_Syntax_Syntax.Tm_type (uu____1345))
in (FStar_Syntax_Syntax.mk uu____1344))
in (uu____1337 FStar_Pervasives_Native.None uu____1336)))
end
| uu____1355 -> begin
(

let uu____1356 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed ((t0), (s)) uu____1356))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___41_1368 -> (match (uu___41_1368) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(

let uu____1372 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (uu____1372))
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
| uu____1406 -> begin
(

let uu___46_1417 = t
in (

let uu____1418 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____1425 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____1430 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____1433 = (FStar_List.map (fun uu____1458 -> (match (uu____1458) with
| (t1, imp) -> begin
(

let uu____1477 = (subst' s t1)
in ((uu____1477), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (

let uu____1482 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu____1418; FStar_Syntax_Syntax.effect_name = uu____1425; FStar_Syntax_Syntax.result_typ = uu____1430; FStar_Syntax_Syntax.effect_args = uu____1433; FStar_Syntax_Syntax.flags = uu____1482}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp = (fun s t -> (match (s) with
| ([], FStar_Pervasives_Native.None) -> begin
t
end
| (([])::[], FStar_Pervasives_Native.None) -> begin
t
end
| uu____1517 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uopt) -> begin
(

let uu____1538 = (subst' s t1)
in (

let uu____1539 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____1538 uu____1539)))
end
| FStar_Syntax_Syntax.GTotal (t1, uopt) -> begin
(

let uu____1558 = (subst' s t1)
in (

let uu____1559 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1558 uu____1559)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1569 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp uu____1569))
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
| FStar_Syntax_Syntax.NT (uu____1588) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n1 s -> (FStar_List.map (shift n1) s))


let shift_subst' : 'Auu____1611 . Prims.int  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1611)  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1611) = (fun n1 s -> (

let uu____1640 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (shift_subst n1)))
in ((uu____1640), ((FStar_Pervasives_Native.snd s)))))


let subst_binder' : 'Auu____1659 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.bv * 'Auu____1659)  ->  (FStar_Syntax_Syntax.bv * 'Auu____1659) = (fun s uu____1677 -> (match (uu____1677) with
| (x, imp) -> begin
(

let uu____1684 = (

let uu___47_1685 = x
in (

let uu____1686 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___47_1685.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___47_1685.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1686}))
in ((uu____1684), (imp)))
end))


let subst_binders' : 'Auu____1695 . (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.bv * 'Auu____1695) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____1695) Prims.list = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1772 -> begin
(

let uu____1773 = (shift_subst' i s)
in (subst_binder' uu____1773 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (FStar_Pervasives_Native.None)) bs))


let subst_arg' : 'Auu____1800 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1800)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1800) = (fun s uu____1822 -> (match (uu____1822) with
| (t, imp) -> begin
(

let uu____1835 = (subst' s t)
in ((uu____1835), (imp)))
end))


let subst_args' : 'Auu____1845 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1845) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1845) Prims.list = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____1944) -> begin
((p1), (n1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1963 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____2017 uu____2018 -> (match (((uu____2017), (uu____2018))) with
| ((pats1, n2), (p2, imp)) -> begin
(

let uu____2097 = (aux n2 p2)
in (match (uu____2097) with
| (p3, m) -> begin
(((((p3), (imp)))::pats1), (m))
end))
end)) (([]), (n1))))
in (match (uu____1963) with
| (pats1, n2) -> begin
(((

let uu___48_2153 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___48_2153.FStar_Syntax_Syntax.p})), (n2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___49_2183 = x
in (

let uu____2184 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___49_2183.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___49_2183.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2184}))
in (((

let uu___50_2188 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___50_2188.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___51_2204 = x
in (

let uu____2205 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___51_2204.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___51_2204.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2205}))
in (((

let uu___52_2209 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___52_2209.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___53_2230 = x
in (

let uu____2231 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___53_2230.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___53_2230.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2231}))
in (

let t01 = (subst' s1 t0)
in (((

let uu___54_2238 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___54_2238.FStar_Syntax_Syntax.p})), (n1)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s lopt -> (match (lopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____2262 = (

let uu___55_2263 = rc
in (

let uu____2264 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (subst' s))
in {FStar_Syntax_Syntax.residual_effect = uu___55_2263.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____2264; FStar_Syntax_Syntax.residual_flags = uu___55_2263.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____2262))
end))


let rec push_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk1 = (fun t' -> (

let uu____2297 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2297)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2300) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
t
end
| FStar_Syntax_Syntax.Tm_constant (uu____2328) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2333) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_uvar ({FStar_Syntax_Syntax.ctx_uvar_head = uv; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____2343; FStar_Syntax_Syntax.ctx_uvar_binders = uu____2344; FStar_Syntax_Syntax.ctx_uvar_typ = uu____2345; FStar_Syntax_Syntax.ctx_uvar_reason = uu____2346; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____2347; FStar_Syntax_Syntax.ctx_uvar_range = uu____2348}) -> begin
(

let uu____2369 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____2369) with
| FStar_Pervasives_Native.None -> begin
(tag_with_range t s)
end
| FStar_Pervasives_Native.Some (t1) -> begin
(push_subst s t1)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____2379) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2380) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_name (uu____2381) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us1 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us)
in (

let uu____2397 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us1)
in (tag_with_range uu____2397 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(

let uu____2426 = (

let uu____2427 = (

let uu____2442 = (subst' s t0)
in (

let uu____2445 = (subst_args' s args)
in ((uu____2442), (uu____2445))))
in FStar_Syntax_Syntax.Tm_app (uu____2427))
in (mk1 uu____2426))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t1) -> begin
(

let uu____2540 = (subst' s t1)
in FStar_Util.Inl (uu____2540))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2554 = (subst_comp' s c)
in FStar_Util.Inr (uu____2554))
end)
in (

let uu____2557 = (

let uu____2558 = (

let uu____2585 = (subst' s t0)
in (

let uu____2588 = (

let uu____2605 = (FStar_Util.map_opt topt (subst' s))
in ((annot1), (uu____2605)))
in ((uu____2585), (uu____2588), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2558))
in (mk1 uu____2557)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n1 = (FStar_List.length bs)
in (

let s' = (shift_subst' n1 s)
in (

let uu____2689 = (

let uu____2690 = (

let uu____2707 = (subst_binders' s bs)
in (

let uu____2714 = (subst' s' body)
in (

let uu____2717 = (push_subst_lcomp s' lopt)
in ((uu____2707), (uu____2714), (uu____2717)))))
in FStar_Syntax_Syntax.Tm_abs (uu____2690))
in (mk1 uu____2689))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n1 = (FStar_List.length bs)
in (

let uu____2753 = (

let uu____2754 = (

let uu____2767 = (subst_binders' s bs)
in (

let uu____2774 = (

let uu____2777 = (shift_subst' n1 s)
in (subst_comp' uu____2777 comp))
in ((uu____2767), (uu____2774))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2754))
in (mk1 uu____2753)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x1 = (

let uu___56_2809 = x
in (

let uu____2810 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___56_2809.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___56_2809.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2810}))
in (

let phi1 = (

let uu____2816 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____2816 phi))
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((x1), (phi1)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t01 = (subst' s t0)
in (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____2943 -> (match (uu____2943) with
| (pat, wopt, branch) -> begin
(

let uu____2989 = (subst_pat' s pat)
in (match (uu____2989) with
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

let uu____3037 = (subst' s1 w)
in FStar_Pervasives_Native.Some (uu____3037))
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

let uu____3124 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____3124) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____3127 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___57_3139 = x
in {FStar_Syntax_Syntax.ppname = uu___57_3139.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___57_3139.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr (fv)
end)
in (

let uu___58_3141 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___58_3141.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___58_3141.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd; FStar_Syntax_Syntax.lbattrs = uu___58_3141.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___58_3141.FStar_Syntax_Syntax.lbpos})))))))
in (mk1 (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs1))), (body1)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let uu____3168 = (

let uu____3169 = (

let uu____3176 = (subst' s t0)
in (

let uu____3179 = (

let uu____3180 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____3180))
in ((uu____3176), (uu____3179))))
in FStar_Syntax_Syntax.Tm_meta (uu____3169))
in (mk1 uu____3168))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) -> begin
(

let uu____3240 = (

let uu____3241 = (

let uu____3248 = (subst' s t0)
in (

let uu____3251 = (

let uu____3252 = (

let uu____3259 = (subst' s t1)
in ((m), (uu____3259)))
in FStar_Syntax_Syntax.Meta_monadic (uu____3252))
in ((uu____3248), (uu____3251))))
in FStar_Syntax_Syntax.Tm_meta (uu____3241))
in (mk1 uu____3240))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) -> begin
(

let uu____3278 = (

let uu____3279 = (

let uu____3286 = (subst' s t0)
in (

let uu____3289 = (

let uu____3290 = (

let uu____3299 = (subst' s t1)
in ((m1), (m2), (uu____3299)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____3290))
in ((uu____3286), (uu____3289))))
in FStar_Syntax_Syntax.Tm_meta (uu____3279))
in (mk1 uu____3278))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____3314 = (

let uu____3315 = (

let uu____3322 = (subst' s tm)
in ((uu____3322), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____3315))
in (mk1 uu____3314))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted (subst' s) qi)
in (mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi1))))))
end)
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____3336 = (

let uu____3337 = (

let uu____3344 = (subst' s t1)
in ((uu____3344), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____3337))
in (mk1 uu____3336))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (try_read_memo t)
in (

let uu____3357 = (force_uvar t1)
in (match (uu____3357) with
| (t2, uu____3363) -> begin
(match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s), memo) -> begin
((

let uu____3416 = (

let uu____3421 = (push_subst s t')
in FStar_Pervasives_Native.Some (uu____3421))
in (FStar_ST.op_Colon_Equals memo uu____3416));
(compress t2);
)
end
| uu____3479 -> begin
t2
end)
end))))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (

let uu____3514 = (

let uu____3515 = (

let uu____3518 = (

let uu____3519 = (FStar_Range.use_range r)
in (FStar_Range.set_def_range r uu____3519))
in FStar_Pervasives_Native.Some (uu____3518))
in (([]), (uu____3515)))
in (subst' uu____3514 t)))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let closing_subst : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun bs -> (

let uu____3559 = (FStar_List.fold_right (fun uu____3582 uu____3583 -> (match (((uu____3582), (uu____3583))) with
| ((x, uu____3611), (subst1, n1)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n1))))::subst1), ((n1 + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____3559 FStar_Pervasives_Native.fst)))


let open_binders' : 'Auu____3646 . (FStar_Syntax_Syntax.bv * 'Auu____3646) Prims.list  ->  ((FStar_Syntax_Syntax.bv * 'Auu____3646) Prims.list * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun bs -> (

let rec aux = (fun bs1 o -> (match (bs1) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___59_3757 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____3758 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___59_3757.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___59_3757.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3758}))
in (

let o1 = (

let uu____3764 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____3764)
in (

let uu____3767 = (aux bs' o1)
in (match (uu____3767) with
| (bs'1, o2) -> begin
(((((x'), (imp)))::bs'1), (o2))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____3827 = (open_binders' bs)
in (FStar_Pervasives_Native.fst uu____3827)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____3864 = (open_binders' bs)
in (match (uu____3864) with
| (bs', opening) -> begin
(

let uu____3901 = (subst opening t)
in ((bs'), (uu____3901), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____3916 = (open_term' bs t)
in (match (uu____3916) with
| (b, t1, uu____3929) -> begin
((b), (t1))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____3944 = (open_binders' bs)
in (match (uu____3944) with
| (bs', opening) -> begin
(

let uu____3979 = (subst_comp opening t)
in ((bs'), (uu____3979)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec open_pat_aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4020) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4041 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4101 uu____4102 -> (match (((uu____4101), (uu____4102))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____4193 = (open_pat_aux sub2 p2)
in (match (uu____4193) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4041) with
| (pats1, sub2) -> begin
(((

let uu___60_4275 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___60_4275.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___61_4294 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4295 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___61_4294.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___61_4294.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4295}))
in (

let sub2 = (

let uu____4301 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4301)
in (((

let uu___62_4307 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.p = uu___62_4307.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___63_4312 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4313 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___63_4312.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___63_4312.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4313}))
in (

let sub2 = (

let uu____4319 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4319)
in (((

let uu___64_4325 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.p = uu___64_4325.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___65_4335 = x
in (

let uu____4336 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___65_4335.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___65_4335.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4336}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___66_4343 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___66_4343.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (open_pat_aux [] p)))


let open_branch' : FStar_Syntax_Syntax.branch  ->  (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t) = (fun uu____4356 -> (match (uu____4356) with
| (p, wopt, e) -> begin
(

let uu____4380 = (open_pat p)
in (match (uu____4380) with
| (p1, opening) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____4403 = (subst opening w)
in FStar_Pervasives_Native.Some (uu____4403))
end)
in (

let e1 = (subst opening e)
in ((((p1), (wopt1), (e1))), (opening))))
end))
end))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun br -> (

let uu____4414 = (open_branch' br)
in (match (uu____4414) with
| (br1, uu____4420) -> begin
br1
end)))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____4431 = (closing_subst bs)
in (subst uu____4431 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____4444 = (closing_subst bs)
in (subst_comp uu____4444 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs1 -> (match (bs1) with
| [] -> begin
[]
end
| ((x, imp))::tl1 -> begin
(

let x1 = (

let uu___67_4501 = x
in (

let uu____4502 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___67_4501.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___67_4501.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4502}))
in (

let s' = (

let uu____4508 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____4508)
in (

let uu____4511 = (aux s' tl1)
in (((x1), (imp)))::uu____4511)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____4537 -> (

let uu____4538 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (subst_comp s uu____4538))))))


let close_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4581) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4602 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4662 uu____4663 -> (match (((uu____4662), (uu____4663))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____4754 = (aux sub2 p2)
in (match (uu____4754) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4602) with
| (pats1, sub2) -> begin
(((

let uu___68_4836 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___68_4836.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___69_4855 = x
in (

let uu____4856 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___69_4855.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___69_4855.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4856}))
in (

let sub2 = (

let uu____4862 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____4862)
in (((

let uu___70_4868 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___70_4868.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___71_4873 = x
in (

let uu____4874 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___71_4873.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___71_4873.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4874}))
in (

let sub2 = (

let uu____4880 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____4880)
in (((

let uu___72_4886 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___72_4886.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___73_4896 = x
in (

let uu____4897 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___73_4896.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___73_4896.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4897}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___74_4904 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___74_4904.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____4913 -> (match (uu____4913) with
| (p, wopt, e) -> begin
(

let uu____4933 = (close_pat p)
in (match (uu____4933) with
| (p1, closing) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____4958 = (subst closing w)
in FStar_Pervasives_Native.Some (uu____4958))
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

let uu____5027 = (univ_var_opening us)
in (match (uu____5027) with
| (s, us') -> begin
(

let t1 = (subst s t)
in ((us'), (t1)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____5069 = (univ_var_opening us)
in (match (uu____5069) with
| (s, us') -> begin
(

let uu____5092 = (subst_comp s c)
in ((us'), (uu____5092)))
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

let uu____5146 = (

let uu____5157 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5157) with
| true -> begin
(((Prims.parse_int "0")), (lbs), ([]))
end
| uu____5172 -> begin
(FStar_List.fold_right (fun lb uu____5190 -> (match (uu____5190) with
| (i, lbs1, out) -> begin
(

let x = (

let uu____5223 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____5223))
in (((i + (Prims.parse_int "1"))), (((

let uu___75_5229 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___75_5229.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___75_5229.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___75_5229.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___75_5229.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___75_5229.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___75_5229.FStar_Syntax_Syntax.lbpos}))::lbs1), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
end))
in (match (uu____5146) with
| (n_let_recs, lbs1, let_rec_opening) -> begin
(

let lbs2 = (FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let uu____5267 = (FStar_List.fold_right (fun u uu____5295 -> (match (uu____5295) with
| (i, us, out) -> begin
(

let u1 = (FStar_Syntax_Syntax.new_univ_name FStar_Pervasives_Native.None)
in (((i + (Prims.parse_int "1"))), ((u1)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u1)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____5267) with
| (uu____5336, us, u_let_rec_opening) -> begin
(

let uu___76_5347 = lb
in (

let uu____5348 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____5351 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___76_5347.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu____5348; FStar_Syntax_Syntax.lbeff = uu___76_5347.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5351; FStar_Syntax_Syntax.lbattrs = uu___76_5347.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___76_5347.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_opening t)
in ((lbs2), (t1))))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____5377 = (

let uu____5384 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5384) with
| true -> begin
(((Prims.parse_int "0")), ([]))
end
| uu____5393 -> begin
(FStar_List.fold_right (fun lb uu____5406 -> (match (uu____5406) with
| (i, out) -> begin
(

let uu____5425 = (

let uu____5428 = (

let uu____5429 = (

let uu____5434 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____5434), (i)))
in FStar_Syntax_Syntax.NM (uu____5429))
in (uu____5428)::out)
in (((i + (Prims.parse_int "1"))), (uu____5425)))
end)) lbs (((Prims.parse_int "0")), ([])))
end))
in (match (uu____5377) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____5466 = (FStar_List.fold_right (fun u uu____5484 -> (match (uu____5484) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____5466) with
| (uu____5507, u_let_rec_closing) -> begin
(

let uu___77_5513 = lb
in (

let uu____5514 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____5517 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___77_5513.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___77_5513.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____5514; FStar_Syntax_Syntax.lbeff = uu___77_5513.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5517; FStar_Syntax_Syntax.lbattrs = uu___77_5513.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___77_5513.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_closing t)
in ((lbs1), (t1))))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____5532 -> (match (uu____5532) with
| (us, t) -> begin
(

let n1 = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____5561 -> (match (uu____5561) with
| (x, uu____5567) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n1 - i)))))
end)) binders)
in (

let t1 = (subst s t)
in ((us), (t1))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____5588 -> (match (uu____5588) with
| (us', t) -> begin
(

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n1 - i)))))) us)
in (

let uu____5614 = (subst s t)
in ((us'), (uu____5614))))))
end))


let subst_tscheme : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun s uu____5632 -> (match (uu____5632) with
| (us, t) -> begin
(

let s1 = (shift_subst (FStar_List.length us) s)
in (

let uu____5646 = (subst s1 t)
in ((us), (uu____5646))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n1 = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____5674 -> (match (uu____5674) with
| (x, uu____5680) -> begin
FStar_Syntax_Syntax.DB ((((n1 - i)), (x)))
end))))))


let closing_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (closing_subst bs))


let open_term_1 : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term) = (fun b t -> (

let uu____5700 = (open_term ((b)::[]) t)
in (match (uu____5700) with
| ((b1)::[], t1) -> begin
((b1), (t1))
end
| uu____5731 -> begin
(failwith "impossible: open_term_1")
end)))


let open_term_bvs : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun bvs t -> (

let uu____5760 = (

let uu____5765 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (open_term uu____5765 t))
in (match (uu____5760) with
| (bs, t1) -> begin
(

let uu____5778 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in ((uu____5778), (t1)))
end)))


let open_term_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun bv t -> (

let uu____5801 = (open_term_bvs ((bv)::[]) t)
in (match (uu____5801) with
| ((bv1)::[], t1) -> begin
((bv1), (t1))
end
| uu____5816 -> begin
(failwith "impossible: open_term_bv")
end)))




