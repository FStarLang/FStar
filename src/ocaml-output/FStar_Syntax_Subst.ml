
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


let force_uvar : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * Prims.bool) = (fun t -> (

let uu____541 = (force_uvar' t)
in (match (uu____541) with
| (t', forced) -> begin
(match ((not (forced))) with
| true -> begin
((t), (forced))
end
| uu____562 -> begin
(

let uu____563 = (delay t' (([]), (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))))
in ((uu____563), (forced)))
end)
end)))


let rec try_read_memo_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(

let uu____635 = (FStar_ST.op_Bang m)
in (match (uu____635) with
| FStar_Pervasives_Native.None -> begin
((t), (false))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____708 = (try_read_memo_aux t')
in (match (uu____708) with
| (t'1, shorten) -> begin
((match (shorten) with
| true -> begin
(FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some (t'1)))
end
| uu____783 -> begin
()
end);
((t'1), (true));
)
end))
end))
end
| uu____786 -> begin
((t), (false))
end))


let try_read_memo : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____800 = (try_read_memo_aux t)
in (FStar_Pervasives_Native.fst uu____800)))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(

let uu____823 = (FStar_Syntax_Unionfind.univ_find u')
in (match (uu____823) with
| FStar_Pervasives_Native.Some (u1) -> begin
(compress_univ u1)
end
| uu____827 -> begin
u
end))
end
| uu____830 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___37_851 -> (match (uu___37_851) with
| FStar_Syntax_Syntax.DB (i, x) when (Prims.op_Equality i a.FStar_Syntax_Syntax.index) -> begin
(

let uu____856 = (

let uu____857 = (

let uu____858 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x uu____858))
in (FStar_Syntax_Syntax.bv_to_name uu____857))
in FStar_Pervasives_Native.Some (uu____856))
end
| uu____859 -> begin
FStar_Pervasives_Native.None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___38_884 -> (match (uu___38_884) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____891 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___42_896 = a
in {FStar_Syntax_Syntax.ppname = uu___42_896.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___42_896.FStar_Syntax_Syntax.sort}))
in FStar_Pervasives_Native.Some (uu____891))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____907 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___39_929 -> (match (uu___39_929) with
| FStar_Syntax_Syntax.UN (y, t) when (Prims.op_Equality x y) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____934 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___40_954 -> (match (uu___40_954) with
| FStar_Syntax_Syntax.UD (y, i) when (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____959 -> begin
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
| FStar_Syntax_Syntax.U_unif (uu____985) -> begin
u1
end
| FStar_Syntax_Syntax.U_succ (u2) -> begin
(

let uu____995 = (subst_univ s u2)
in FStar_Syntax_Syntax.U_succ (uu____995))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____999 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (uu____999))
end)))


let tag_with_range : 'Auu____1008 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ('Auu____1008 * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
t
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let r1 = (

let uu____1041 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1041))
in (

let t' = (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____1044 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_bvar (uu____1044))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____1046 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_name (uu____1046))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v1 = (

let uu___43_1052 = fv.FStar_Syntax_Syntax.fv_name
in (

let uu____1053 = (FStar_Ident.set_lid_range l r1)
in {FStar_Syntax_Syntax.v = uu____1053; FStar_Syntax_Syntax.p = uu___43_1052.FStar_Syntax_Syntax.p}))
in (

let fv1 = (

let uu___44_1055 = fv
in {FStar_Syntax_Syntax.fv_name = v1; FStar_Syntax_Syntax.fv_delta = uu___44_1055.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___44_1055.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv1))))
end
| t' -> begin
t'
end)
in (

let uu___45_1057 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___45_1057.FStar_Syntax_Syntax.vars})))
end))


let tag_lid_with_range : 'Auu____1066 . FStar_Ident.lident  ->  ('Auu____1066 * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Ident.lident = (fun l s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____1092 = (

let uu____1093 = (FStar_Ident.range_of_lid l)
in (

let uu____1094 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range uu____1093 uu____1094)))
in (FStar_Ident.set_lid_range l uu____1092))
end))


let mk_range : FStar_Range.range  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Range.range = (fun r s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
r
end
| FStar_Pervasives_Native.Some (r') -> begin
(

let uu____1112 = (FStar_Range.use_range r')
in (FStar_Range.set_use_range r uu____1112))
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
| uu____1236 -> begin
(

let t0 = (try_read_memo t)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1246) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1251) -> begin
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

let uu____1334 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (

let uu____1335 = (

let uu____1342 = (

let uu____1343 = (subst_univ (FStar_Pervasives_Native.fst s) u)
in FStar_Syntax_Syntax.Tm_type (uu____1343))
in (FStar_Syntax_Syntax.mk uu____1342))
in (uu____1335 FStar_Pervasives_Native.None uu____1334)))
end
| uu____1353 -> begin
(

let uu____1354 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed ((t0), (s)) uu____1354))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___41_1366 -> (match (uu___41_1366) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(

let uu____1370 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (uu____1370))
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
| uu____1404 -> begin
(

let uu___46_1415 = t
in (

let uu____1416 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____1423 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____1428 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____1431 = (FStar_List.map (fun uu____1456 -> (match (uu____1456) with
| (t1, imp) -> begin
(

let uu____1475 = (subst' s t1)
in ((uu____1475), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (

let uu____1480 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu____1416; FStar_Syntax_Syntax.effect_name = uu____1423; FStar_Syntax_Syntax.result_typ = uu____1428; FStar_Syntax_Syntax.effect_args = uu____1431; FStar_Syntax_Syntax.flags = uu____1480}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
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

let uu____1540 = (subst' s t1)
in (

let uu____1541 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____1540 uu____1541)))
end
| FStar_Syntax_Syntax.GTotal (t1, uopt) -> begin
(

let uu____1560 = (subst' s t1)
in (

let uu____1561 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1560 uu____1561)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1571 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp uu____1571))
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
| FStar_Syntax_Syntax.NT (uu____1590) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n1 s -> (FStar_List.map (shift n1) s))


let shift_subst' : 'Auu____1613 . Prims.int  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1613)  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1613) = (fun n1 s -> (

let uu____1642 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (shift_subst n1)))
in ((uu____1642), ((FStar_Pervasives_Native.snd s)))))


let subst_binder' : 'Auu____1661 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.bv * 'Auu____1661)  ->  (FStar_Syntax_Syntax.bv * 'Auu____1661) = (fun s uu____1679 -> (match (uu____1679) with
| (x, imp) -> begin
(

let uu____1686 = (

let uu___47_1687 = x
in (

let uu____1688 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___47_1687.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___47_1687.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1688}))
in ((uu____1686), (imp)))
end))


let subst_binders' : 'Auu____1697 . (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.bv * 'Auu____1697) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____1697) Prims.list = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1778 -> begin
(

let uu____1779 = (shift_subst' i s)
in (subst_binder' uu____1779 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (FStar_Pervasives_Native.None)) bs))


let subst_arg' : 'Auu____1812 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1812)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1812) = (fun s uu____1834 -> (match (uu____1834) with
| (t, imp) -> begin
(

let uu____1847 = (subst' s t)
in ((uu____1847), (imp)))
end))


let subst_args' : 'Auu____1857 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1857) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1857) Prims.list = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____1956) -> begin
((p1), (n1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1975 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____2029 uu____2030 -> (match (((uu____2029), (uu____2030))) with
| ((pats1, n2), (p2, imp)) -> begin
(

let uu____2109 = (aux n2 p2)
in (match (uu____2109) with
| (p3, m) -> begin
(((((p3), (imp)))::pats1), (m))
end))
end)) (([]), (n1))))
in (match (uu____1975) with
| (pats1, n2) -> begin
(((

let uu___48_2165 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___48_2165.FStar_Syntax_Syntax.p})), (n2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___49_2195 = x
in (

let uu____2196 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___49_2195.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___49_2195.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2196}))
in (((

let uu___50_2200 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___50_2200.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___51_2216 = x
in (

let uu____2217 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___51_2216.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___51_2216.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2217}))
in (((

let uu___52_2221 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___52_2221.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___53_2242 = x
in (

let uu____2243 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___53_2242.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___53_2242.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2243}))
in (

let t01 = (subst' s1 t0)
in (((

let uu___54_2250 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___54_2250.FStar_Syntax_Syntax.p})), (n1)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s lopt -> (match (lopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____2274 = (

let uu___55_2275 = rc
in (

let uu____2276 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (subst' s))
in {FStar_Syntax_Syntax.residual_effect = uu___55_2275.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____2276; FStar_Syntax_Syntax.residual_flags = uu___55_2275.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____2274))
end))


let rec push_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk1 = (fun t' -> (

let uu____2309 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2309)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2312) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
t
end
| FStar_Syntax_Syntax.Tm_constant (uu____2340) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2345) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_uvar ({FStar_Syntax_Syntax.ctx_uvar_head = uv; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____2355; FStar_Syntax_Syntax.ctx_uvar_binders = uu____2356; FStar_Syntax_Syntax.ctx_uvar_typ = uu____2357; FStar_Syntax_Syntax.ctx_uvar_reason = uu____2358; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____2359; FStar_Syntax_Syntax.ctx_uvar_range = uu____2360}) -> begin
(

let uu____2381 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____2381) with
| FStar_Pervasives_Native.None -> begin
(tag_with_range t s)
end
| FStar_Pervasives_Native.Some (t1) -> begin
(push_subst s t1)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____2391) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2392) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_name (uu____2393) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us1 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us)
in (

let uu____2409 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us1)
in (tag_with_range uu____2409 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(

let uu____2438 = (

let uu____2439 = (

let uu____2454 = (subst' s t0)
in (

let uu____2457 = (subst_args' s args)
in ((uu____2454), (uu____2457))))
in FStar_Syntax_Syntax.Tm_app (uu____2439))
in (mk1 uu____2438))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t1) -> begin
(

let uu____2552 = (subst' s t1)
in FStar_Util.Inl (uu____2552))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2566 = (subst_comp' s c)
in FStar_Util.Inr (uu____2566))
end)
in (

let uu____2573 = (

let uu____2574 = (

let uu____2601 = (subst' s t0)
in (

let uu____2604 = (

let uu____2621 = (FStar_Util.map_opt topt (subst' s))
in ((annot1), (uu____2621)))
in ((uu____2601), (uu____2604), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2574))
in (mk1 uu____2573)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n1 = (FStar_List.length bs)
in (

let s' = (shift_subst' n1 s)
in (

let uu____2705 = (

let uu____2706 = (

let uu____2723 = (subst_binders' s bs)
in (

let uu____2730 = (subst' s' body)
in (

let uu____2733 = (push_subst_lcomp s' lopt)
in ((uu____2723), (uu____2730), (uu____2733)))))
in FStar_Syntax_Syntax.Tm_abs (uu____2706))
in (mk1 uu____2705))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n1 = (FStar_List.length bs)
in (

let uu____2769 = (

let uu____2770 = (

let uu____2783 = (subst_binders' s bs)
in (

let uu____2790 = (

let uu____2793 = (shift_subst' n1 s)
in (subst_comp' uu____2793 comp))
in ((uu____2783), (uu____2790))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2770))
in (mk1 uu____2769)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x1 = (

let uu___56_2825 = x
in (

let uu____2826 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___56_2825.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___56_2825.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2826}))
in (

let phi1 = (

let uu____2832 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____2832 phi))
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((x1), (phi1)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t01 = (subst' s t0)
in (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____2963 -> (match (uu____2963) with
| (pat, wopt, branch) -> begin
(

let uu____3009 = (subst_pat' s pat)
in (match (uu____3009) with
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

let uu____3057 = (subst' s1 w)
in FStar_Pervasives_Native.Some (uu____3057))
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

let uu____3144 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____3144) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____3147 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___57_3159 = x
in {FStar_Syntax_Syntax.ppname = uu___57_3159.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___57_3159.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr (fv)
end)
in (

let uu___58_3161 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___58_3161.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___58_3161.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd; FStar_Syntax_Syntax.lbattrs = uu___58_3161.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___58_3161.FStar_Syntax_Syntax.lbpos})))))))
in (mk1 (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs1))), (body1)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let uu____3188 = (

let uu____3189 = (

let uu____3196 = (subst' s t0)
in (

let uu____3199 = (

let uu____3200 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____3200))
in ((uu____3196), (uu____3199))))
in FStar_Syntax_Syntax.Tm_meta (uu____3189))
in (mk1 uu____3188))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) -> begin
(

let uu____3260 = (

let uu____3261 = (

let uu____3268 = (subst' s t0)
in (

let uu____3271 = (

let uu____3272 = (

let uu____3279 = (subst' s t1)
in ((m), (uu____3279)))
in FStar_Syntax_Syntax.Meta_monadic (uu____3272))
in ((uu____3268), (uu____3271))))
in FStar_Syntax_Syntax.Tm_meta (uu____3261))
in (mk1 uu____3260))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) -> begin
(

let uu____3298 = (

let uu____3299 = (

let uu____3306 = (subst' s t0)
in (

let uu____3309 = (

let uu____3310 = (

let uu____3319 = (subst' s t1)
in ((m1), (m2), (uu____3319)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____3310))
in ((uu____3306), (uu____3309))))
in FStar_Syntax_Syntax.Tm_meta (uu____3299))
in (mk1 uu____3298))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____3334 = (

let uu____3335 = (

let uu____3342 = (subst' s tm)
in ((uu____3342), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____3335))
in (mk1 uu____3334))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted (subst' s) qi)
in (mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi1))))))
end)
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____3356 = (

let uu____3357 = (

let uu____3364 = (subst' s t1)
in ((uu____3364), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____3357))
in (mk1 uu____3356))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (try_read_memo t)
in (

let uu____3377 = (force_uvar t1)
in (match (uu____3377) with
| (t2, uu____3383) -> begin
(match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s), memo) -> begin
((

let uu____3436 = (

let uu____3441 = (push_subst s t')
in FStar_Pervasives_Native.Some (uu____3441))
in (FStar_ST.op_Colon_Equals memo uu____3436));
(compress t2);
)
end
| uu____3499 -> begin
t2
end)
end))))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (

let uu____3534 = (

let uu____3535 = (

let uu____3538 = (

let uu____3539 = (FStar_Range.use_range r)
in (FStar_Range.set_def_range r uu____3539))
in FStar_Pervasives_Native.Some (uu____3538))
in (([]), (uu____3535)))
in (subst' uu____3534 t)))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let closing_subst : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun bs -> (

let uu____3579 = (FStar_List.fold_right (fun uu____3602 uu____3603 -> (match (((uu____3602), (uu____3603))) with
| ((x, uu____3631), (subst1, n1)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n1))))::subst1), ((n1 + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____3579 FStar_Pervasives_Native.fst)))


let open_binders' : 'Auu____3666 . (FStar_Syntax_Syntax.bv * 'Auu____3666) Prims.list  ->  ((FStar_Syntax_Syntax.bv * 'Auu____3666) Prims.list * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun bs -> (

let rec aux = (fun bs1 o -> (match (bs1) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___59_3777 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____3778 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___59_3777.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___59_3777.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3778}))
in (

let o1 = (

let uu____3784 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____3784)
in (

let uu____3787 = (aux bs' o1)
in (match (uu____3787) with
| (bs'1, o2) -> begin
(((((x'), (imp)))::bs'1), (o2))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____3847 = (open_binders' bs)
in (FStar_Pervasives_Native.fst uu____3847)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____3884 = (open_binders' bs)
in (match (uu____3884) with
| (bs', opening) -> begin
(

let uu____3921 = (subst opening t)
in ((bs'), (uu____3921), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____3936 = (open_term' bs t)
in (match (uu____3936) with
| (b, t1, uu____3949) -> begin
((b), (t1))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____3964 = (open_binders' bs)
in (match (uu____3964) with
| (bs', opening) -> begin
(

let uu____3999 = (subst_comp opening t)
in ((bs'), (uu____3999)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec open_pat_aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4048) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4071 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4137 uu____4138 -> (match (((uu____4137), (uu____4138))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____4241 = (open_pat_aux sub2 p2)
in (match (uu____4241) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4071) with
| (pats1, sub2) -> begin
(((

let uu___60_4343 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___60_4343.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___61_4362 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4363 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___61_4362.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___61_4362.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4363}))
in (

let sub2 = (

let uu____4369 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4369)
in (((

let uu___62_4377 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.p = uu___62_4377.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___63_4382 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4383 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___63_4382.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___63_4382.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4383}))
in (

let sub2 = (

let uu____4389 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4389)
in (((

let uu___64_4397 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.p = uu___64_4397.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___65_4407 = x
in (

let uu____4408 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___65_4407.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___65_4407.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4408}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___66_4417 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___66_4417.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (open_pat_aux [] p)))


let open_branch' : FStar_Syntax_Syntax.branch  ->  (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t) = (fun uu____4430 -> (match (uu____4430) with
| (p, wopt, e) -> begin
(

let uu____4454 = (open_pat p)
in (match (uu____4454) with
| (p1, opening) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____4483 = (subst opening w)
in FStar_Pervasives_Native.Some (uu____4483))
end)
in (

let e1 = (subst opening e)
in ((((p1), (wopt1), (e1))), (opening))))
end))
end))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun br -> (

let uu____4498 = (open_branch' br)
in (match (uu____4498) with
| (br1, uu____4504) -> begin
br1
end)))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____4515 = (closing_subst bs)
in (subst uu____4515 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____4528 = (closing_subst bs)
in (subst_comp uu____4528 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs1 -> (match (bs1) with
| [] -> begin
[]
end
| ((x, imp))::tl1 -> begin
(

let x1 = (

let uu___67_4585 = x
in (

let uu____4586 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___67_4585.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___67_4585.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4586}))
in (

let s' = (

let uu____4592 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____4592)
in (

let uu____4595 = (aux s' tl1)
in (((x1), (imp)))::uu____4595)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____4621 -> (

let uu____4622 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (subst_comp s uu____4622))))))


let close_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4675) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4698 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4764 uu____4765 -> (match (((uu____4764), (uu____4765))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____4868 = (aux sub2 p2)
in (match (uu____4868) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4698) with
| (pats1, sub2) -> begin
(((

let uu___68_4970 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___68_4970.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___69_4989 = x
in (

let uu____4990 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___69_4989.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___69_4989.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4990}))
in (

let sub2 = (

let uu____4996 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____4996)
in (((

let uu___70_5004 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___70_5004.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___71_5009 = x
in (

let uu____5010 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___71_5009.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___71_5009.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5010}))
in (

let sub2 = (

let uu____5016 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5016)
in (((

let uu___72_5024 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___72_5024.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___73_5034 = x
in (

let uu____5035 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___73_5034.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___73_5034.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5035}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___74_5044 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___74_5044.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____5053 -> (match (uu____5053) with
| (p, wopt, e) -> begin
(

let uu____5073 = (close_pat p)
in (match (uu____5073) with
| (p1, closing) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____5110 = (subst closing w)
in FStar_Pervasives_Native.Some (uu____5110))
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

let uu____5183 = (univ_var_opening us)
in (match (uu____5183) with
| (s, us') -> begin
(

let t1 = (subst s t)
in ((us'), (t1)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____5225 = (univ_var_opening us)
in (match (uu____5225) with
| (s, us') -> begin
(

let uu____5248 = (subst_comp s c)
in ((us'), (uu____5248)))
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

let uu____5304 = (

let uu____5315 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5315) with
| true -> begin
(((Prims.parse_int "0")), (lbs), ([]))
end
| uu____5330 -> begin
(FStar_List.fold_right (fun lb uu____5348 -> (match (uu____5348) with
| (i, lbs1, out) -> begin
(

let x = (

let uu____5381 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____5381))
in (((i + (Prims.parse_int "1"))), (((

let uu___75_5387 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___75_5387.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___75_5387.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___75_5387.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___75_5387.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___75_5387.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___75_5387.FStar_Syntax_Syntax.lbpos}))::lbs1), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
end))
in (match (uu____5304) with
| (n_let_recs, lbs1, let_rec_opening) -> begin
(

let lbs2 = (FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let uu____5425 = (FStar_List.fold_right (fun u uu____5453 -> (match (uu____5453) with
| (i, us, out) -> begin
(

let u1 = (FStar_Syntax_Syntax.new_univ_name FStar_Pervasives_Native.None)
in (((i + (Prims.parse_int "1"))), ((u1)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u1)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____5425) with
| (uu____5494, us, u_let_rec_opening) -> begin
(

let uu___76_5505 = lb
in (

let uu____5506 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____5509 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___76_5505.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu____5506; FStar_Syntax_Syntax.lbeff = uu___76_5505.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5509; FStar_Syntax_Syntax.lbattrs = uu___76_5505.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___76_5505.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_opening t)
in ((lbs2), (t1))))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____5535 = (

let uu____5542 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5542) with
| true -> begin
(((Prims.parse_int "0")), ([]))
end
| uu____5551 -> begin
(FStar_List.fold_right (fun lb uu____5564 -> (match (uu____5564) with
| (i, out) -> begin
(

let uu____5583 = (

let uu____5586 = (

let uu____5587 = (

let uu____5592 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____5592), (i)))
in FStar_Syntax_Syntax.NM (uu____5587))
in (uu____5586)::out)
in (((i + (Prims.parse_int "1"))), (uu____5583)))
end)) lbs (((Prims.parse_int "0")), ([])))
end))
in (match (uu____5535) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____5624 = (FStar_List.fold_right (fun u uu____5642 -> (match (uu____5642) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____5624) with
| (uu____5665, u_let_rec_closing) -> begin
(

let uu___77_5671 = lb
in (

let uu____5672 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____5675 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___77_5671.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___77_5671.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____5672; FStar_Syntax_Syntax.lbeff = uu___77_5671.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5675; FStar_Syntax_Syntax.lbattrs = uu___77_5671.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___77_5671.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_closing t)
in ((lbs1), (t1))))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____5690 -> (match (uu____5690) with
| (us, t) -> begin
(

let n1 = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____5719 -> (match (uu____5719) with
| (x, uu____5725) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n1 - i)))))
end)) binders)
in (

let t1 = (subst s t)
in ((us), (t1))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____5746 -> (match (uu____5746) with
| (us', t) -> begin
(

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n1 - i)))))) us)
in (

let uu____5772 = (subst s t)
in ((us'), (uu____5772))))))
end))


let subst_tscheme : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun s uu____5790 -> (match (uu____5790) with
| (us, t) -> begin
(

let s1 = (shift_subst (FStar_List.length us) s)
in (

let uu____5804 = (subst s1 t)
in ((us), (uu____5804))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n1 = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____5836 -> (match (uu____5836) with
| (x, uu____5842) -> begin
FStar_Syntax_Syntax.DB ((((n1 - i)), (x)))
end))))))


let closing_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (closing_subst bs))


let open_term_1 : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term) = (fun b t -> (

let uu____5862 = (open_term ((b)::[]) t)
in (match (uu____5862) with
| ((b1)::[], t1) -> begin
((b1), (t1))
end
| uu____5893 -> begin
(failwith "impossible: open_term_1")
end)))


let open_term_bvs : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun bvs t -> (

let uu____5922 = (

let uu____5927 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (open_term uu____5927 t))
in (match (uu____5922) with
| (bs, t1) -> begin
(

let uu____5940 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in ((uu____5940), (t1)))
end)))


let open_term_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun bv t -> (

let uu____5963 = (open_term_bvs ((bv)::[]) t)
in (match (uu____5963) with
| ((bv1)::[], t1) -> begin
((bv1), (t1))
end
| uu____5978 -> begin
(failwith "impossible: open_term_bv")
end)))




