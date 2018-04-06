
open Prims
open FStar_Pervasives

let subst_to_string : 'Auu____3 . (FStar_Syntax_Syntax.bv * 'Auu____3) Prims.list  ->  Prims.string = (fun s -> (

let uu____20 = (FStar_All.pipe_right s (FStar_List.map (fun uu____38 -> (match (uu____38) with
| (b, uu____44) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right uu____20 (FStar_String.concat ", "))))


let rec apply_until_some : 'Auu____53 'Auu____54 . ('Auu____53  ->  'Auu____54 FStar_Pervasives_Native.option)  ->  'Auu____53 Prims.list  ->  ('Auu____53 Prims.list * 'Auu____54) FStar_Pervasives_Native.option = (fun f s -> (match (s) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (s0)::rest -> begin
(

let uu____94 = (f s0)
in (match (uu____94) with
| FStar_Pervasives_Native.None -> begin
(apply_until_some f rest)
end
| FStar_Pervasives_Native.Some (st) -> begin
FStar_Pervasives_Native.Some (((rest), (st)))
end))
end))


let map_some_curry : 'Auu____120 'Auu____121 'Auu____122 . ('Auu____120  ->  'Auu____121  ->  'Auu____122)  ->  'Auu____122  ->  ('Auu____120 * 'Auu____121) FStar_Pervasives_Native.option  ->  'Auu____122 = (fun f x uu___37_146 -> (match (uu___37_146) with
| FStar_Pervasives_Native.None -> begin
x
end
| FStar_Pervasives_Native.Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map : 'Auu____174 'Auu____175 'Auu____176 . ('Auu____174  ->  'Auu____175 FStar_Pervasives_Native.option)  ->  'Auu____174 Prims.list  ->  ('Auu____174 Prims.list  ->  'Auu____175  ->  'Auu____176)  ->  'Auu____176  ->  'Auu____176 = (fun f s g t -> (

let uu____220 = (apply_until_some f s)
in (FStar_All.pipe_right uu____220 (map_some_curry g t))))


let compose_subst : 'Auu____243 'Auu____244 . ('Auu____243 Prims.list * 'Auu____244 FStar_Pervasives_Native.option)  ->  ('Auu____243 Prims.list * 'Auu____244 FStar_Pervasives_Native.option)  ->  ('Auu____243 Prims.list * 'Auu____244 FStar_Pervasives_Native.option) = (fun s1 s2 -> (

let s = (FStar_List.append (FStar_Pervasives_Native.fst s1) (FStar_Pervasives_Native.fst s2))
in (

let ropt = (match ((FStar_Pervasives_Native.snd s2)) with
| FStar_Pervasives_Native.Some (uu____313) -> begin
(FStar_Pervasives_Native.snd s2)
end
| uu____318 -> begin
(FStar_Pervasives_Native.snd s1)
end)
in ((s), (ropt)))))


let delay : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term = (fun t s -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t'), ((compose_subst s' s))) t.FStar_Syntax_Syntax.pos)
end
| uu____424 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t), (s)) t.FStar_Syntax_Syntax.pos)
end))


let rec force_uvar' : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____457) -> begin
(

let uu____482 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____482) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____492 = (

let uu____495 = (force_uvar' t')
in (FStar_Pervasives_Native.fst uu____495))
in ((uu____492), (true)))
end
| uu____506 -> begin
((t), (false))
end))
end
| uu____511 -> begin
((t), (false))
end))


let force_uvar : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (

let uu____527 = (force_uvar' t)
in (match (uu____527) with
| (t', forced) -> begin
(match ((not (forced))) with
| true -> begin
((t), (forced))
end
| uu____554 -> begin
(

let uu____555 = (delay t' (([]), (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))))
in ((uu____555), (forced)))
end)
end)))


let rec try_read_memo_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(

let uu____625 = (FStar_ST.op_Bang m)
in (match (uu____625) with
| FStar_Pervasives_Native.None -> begin
((t), (false))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____748 = (try_read_memo_aux t')
in (match (uu____748) with
| (t'1, shorten) -> begin
((match (shorten) with
| true -> begin
(FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some (t'1)))
end
| uu____873 -> begin
()
end);
((t'1), (true));
)
end))
end))
end
| uu____876 -> begin
((t), (false))
end))


let try_read_memo : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____888 = (try_read_memo_aux t)
in (FStar_Pervasives_Native.fst uu____888)))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(

let uu____909 = (FStar_Syntax_Unionfind.univ_find u')
in (match (uu____909) with
| FStar_Pervasives_Native.Some (u1) -> begin
(compress_univ u1)
end
| uu____913 -> begin
u
end))
end
| uu____916 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___38_933 -> (match (uu___38_933) with
| FStar_Syntax_Syntax.DB (i, x) when (Prims.op_Equality i a.FStar_Syntax_Syntax.index) -> begin
(

let uu____938 = (

let uu____939 = (

let uu____940 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x uu____940))
in (FStar_Syntax_Syntax.bv_to_name uu____939))
in FStar_Pervasives_Native.Some (uu____938))
end
| uu____941 -> begin
FStar_Pervasives_Native.None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___39_958 -> (match (uu___39_958) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____963 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___43_966 = a
in {FStar_Syntax_Syntax.ppname = uu___43_966.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___43_966.FStar_Syntax_Syntax.sort}))
in FStar_Pervasives_Native.Some (uu____963))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____975 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___40_991 -> (match (uu___40_991) with
| FStar_Syntax_Syntax.UN (y, t) when (Prims.op_Equality x y) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____996 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___41_1012 -> (match (uu___41_1012) with
| FStar_Syntax_Syntax.UD (y, i) when (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____1017 -> begin
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
| FStar_Syntax_Syntax.U_unif (uu____1039) -> begin
u1
end
| FStar_Syntax_Syntax.U_succ (u2) -> begin
(

let uu____1049 = (subst_univ s u2)
in FStar_Syntax_Syntax.U_succ (uu____1049))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1053 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (uu____1053))
end)))


let tag_with_range : 'Auu____1059 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ('Auu____1059 * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
t
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let r1 = (

let uu____1090 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1090))
in (

let t' = (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____1093 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_bvar (uu____1093))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____1095 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_name (uu____1095))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v1 = (

let uu___44_1101 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1); FStar_Syntax_Syntax.p = uu___44_1101.FStar_Syntax_Syntax.p})
in (

let fv1 = (

let uu___45_1103 = fv
in {FStar_Syntax_Syntax.fv_name = v1; FStar_Syntax_Syntax.fv_delta = uu___45_1103.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___45_1103.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv1))))
end
| t' -> begin
t'
end)
in (

let uu___46_1105 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___46_1105.FStar_Syntax_Syntax.vars})))
end))


let tag_lid_with_range : 'Auu____1111 . FStar_Ident.lident  ->  ('Auu____1111 * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Ident.lident = (fun l s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____1135 = (

let uu____1136 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range (FStar_Ident.range_of_lid l) uu____1136))
in (FStar_Ident.set_lid_range l uu____1135))
end))


let mk_range : FStar_Range.range  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Range.range = (fun r s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Pervasives_Native.None -> begin
r
end
| FStar_Pervasives_Native.Some (r') -> begin
(

let uu____1150 = (FStar_Range.use_range r')
in (FStar_Range.set_use_range r uu____1150))
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
| uu____1253 -> begin
(

let t0 = (try_read_memo t)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1263) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1268) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1273) -> begin
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

let uu____1382 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (

let uu____1383 = (

let uu____1386 = (

let uu____1387 = (subst_univ (FStar_Pervasives_Native.fst s) u)
in FStar_Syntax_Syntax.Tm_type (uu____1387))
in (FStar_Syntax_Syntax.mk uu____1386))
in (uu____1383 FStar_Pervasives_Native.None uu____1382)))
end
| uu____1397 -> begin
(

let uu____1398 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed ((t0), (s)) uu____1398))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___42_1412 -> (match (uu___42_1412) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(

let uu____1416 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (uu____1416))
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
| uu____1450 -> begin
(

let uu___47_1461 = t
in (

let uu____1462 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____1469 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____1474 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____1477 = (FStar_List.map (fun uu____1502 -> (match (uu____1502) with
| (t1, imp) -> begin
(

let uu____1521 = (subst' s t1)
in ((uu____1521), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (

let uu____1526 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu____1462; FStar_Syntax_Syntax.effect_name = uu____1469; FStar_Syntax_Syntax.result_typ = uu____1474; FStar_Syntax_Syntax.effect_args = uu____1477; FStar_Syntax_Syntax.flags = uu____1526}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([], FStar_Pervasives_Native.None) -> begin
t
end
| (([])::[], FStar_Pervasives_Native.None) -> begin
t
end
| uu____1563 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uopt) -> begin
(

let uu____1586 = (subst' s t1)
in (

let uu____1587 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____1586 uu____1587)))
end
| FStar_Syntax_Syntax.GTotal (t1, uopt) -> begin
(

let uu____1606 = (subst' s t1)
in (

let uu____1607 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1606 uu____1607)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1617 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp uu____1617))
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
| FStar_Syntax_Syntax.NT (uu____1632) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n1 s -> (FStar_List.map (shift n1) s))


let shift_subst' : 'Auu____1648 . Prims.int  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1648)  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1648) = (fun n1 s -> (

let uu____1675 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (shift_subst n1)))
in ((uu____1675), ((FStar_Pervasives_Native.snd s)))))


let subst_binder' : 'Auu____1691 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.bv * 'Auu____1691)  ->  (FStar_Syntax_Syntax.bv * 'Auu____1691) = (fun s uu____1707 -> (match (uu____1707) with
| (x, imp) -> begin
(

let uu____1714 = (

let uu___48_1715 = x
in (

let uu____1716 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___48_1715.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___48_1715.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1716}))
in ((uu____1714), (imp)))
end))


let subst_binders' : 'Auu____1722 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.bv * 'Auu____1722) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____1722) Prims.list = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1781 -> begin
(

let uu____1782 = (shift_subst' i s)
in (subst_binder' uu____1782 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (FStar_Pervasives_Native.None)) bs))


let subst_arg' : 'Auu____1808 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1808)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1808) = (fun s uu____1828 -> (match (uu____1828) with
| (t, imp) -> begin
(

let uu____1841 = (subst' s t)
in ((uu____1841), (imp)))
end))


let subst_args' : 'Auu____1848 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1848) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1848) Prims.list = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____1936) -> begin
((p1), (n1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1957 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____2011 uu____2012 -> (match (((uu____2011), (uu____2012))) with
| ((pats1, n2), (p2, imp)) -> begin
(

let uu____2091 = (aux n2 p2)
in (match (uu____2091) with
| (p3, m) -> begin
(((((p3), (imp)))::pats1), (m))
end))
end)) (([]), (n1))))
in (match (uu____1957) with
| (pats1, n2) -> begin
(((

let uu___49_2149 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___49_2149.FStar_Syntax_Syntax.p})), (n2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___50_2175 = x
in (

let uu____2176 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___50_2175.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___50_2175.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2176}))
in (((

let uu___51_2182 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___51_2182.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___52_2198 = x
in (

let uu____2199 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___52_2198.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___52_2198.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2199}))
in (((

let uu___53_2205 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___53_2205.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___54_2226 = x
in (

let uu____2227 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___54_2226.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___54_2226.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2227}))
in (

let t01 = (subst' s1 t0)
in (((

let uu___55_2236 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___55_2236.FStar_Syntax_Syntax.p})), (n1)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s lopt -> (match (lopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____2256 = (

let uu___56_2257 = rc
in (

let uu____2258 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (subst' s))
in {FStar_Syntax_Syntax.residual_effect = uu___56_2257.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____2258; FStar_Syntax_Syntax.residual_flags = uu___56_2257.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____2256))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk1 = (fun t' -> (

let uu____2285 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2285)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2288) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
t
end
| FStar_Syntax_Syntax.Tm_constant (uu____2316) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2321) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2326) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_type (uu____2351) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2352) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_name (uu____2353) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us1 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us)
in (

let uu____2369 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us1)
in (tag_with_range uu____2369 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(

let uu____2398 = (

let uu____2399 = (

let uu____2414 = (subst' s t0)
in (

let uu____2417 = (subst_args' s args)
in ((uu____2414), (uu____2417))))
in FStar_Syntax_Syntax.Tm_app (uu____2399))
in (mk1 uu____2398))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t1) -> begin
(

let uu____2512 = (subst' s t1)
in FStar_Util.Inl (uu____2512))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2526 = (subst_comp' s c)
in FStar_Util.Inr (uu____2526))
end)
in (

let uu____2533 = (

let uu____2534 = (

let uu____2561 = (subst' s t0)
in (

let uu____2564 = (

let uu____2581 = (FStar_Util.map_opt topt (subst' s))
in ((annot1), (uu____2581)))
in ((uu____2561), (uu____2564), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2534))
in (mk1 uu____2533)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n1 = (FStar_List.length bs)
in (

let s' = (shift_subst' n1 s)
in (

let uu____2665 = (

let uu____2666 = (

let uu____2683 = (subst_binders' s bs)
in (

let uu____2690 = (subst' s' body)
in (

let uu____2693 = (push_subst_lcomp s' lopt)
in ((uu____2683), (uu____2690), (uu____2693)))))
in FStar_Syntax_Syntax.Tm_abs (uu____2666))
in (mk1 uu____2665))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n1 = (FStar_List.length bs)
in (

let uu____2729 = (

let uu____2730 = (

let uu____2743 = (subst_binders' s bs)
in (

let uu____2750 = (

let uu____2753 = (shift_subst' n1 s)
in (subst_comp' uu____2753 comp))
in ((uu____2743), (uu____2750))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2730))
in (mk1 uu____2729)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x1 = (

let uu___57_2785 = x
in (

let uu____2786 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___57_2785.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___57_2785.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2786}))
in (

let phi1 = (

let uu____2792 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____2792 phi))
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((x1), (phi1)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t01 = (subst' s t0)
in (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____2919 -> (match (uu____2919) with
| (pat, wopt, branch) -> begin
(

let uu____2965 = (subst_pat' s pat)
in (match (uu____2965) with
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

let uu____3013 = (subst' s1 w)
in FStar_Pervasives_Native.Some (uu____3013))
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

let uu____3098 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____3098) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____3101 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___58_3113 = x
in {FStar_Syntax_Syntax.ppname = uu___58_3113.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___58_3113.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr (fv)
end)
in (

let uu___59_3115 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___59_3115.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___59_3115.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd; FStar_Syntax_Syntax.lbattrs = uu___59_3115.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___59_3115.FStar_Syntax_Syntax.lbpos})))))))
in (mk1 (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs1))), (body1)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let uu____3142 = (

let uu____3143 = (

let uu____3150 = (subst' s t0)
in (

let uu____3153 = (

let uu____3154 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____3154))
in ((uu____3150), (uu____3153))))
in FStar_Syntax_Syntax.Tm_meta (uu____3143))
in (mk1 uu____3142))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) -> begin
(

let uu____3214 = (

let uu____3215 = (

let uu____3222 = (subst' s t0)
in (

let uu____3225 = (

let uu____3226 = (

let uu____3233 = (subst' s t1)
in ((m), (uu____3233)))
in FStar_Syntax_Syntax.Meta_monadic (uu____3226))
in ((uu____3222), (uu____3225))))
in FStar_Syntax_Syntax.Tm_meta (uu____3215))
in (mk1 uu____3214))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) -> begin
(

let uu____3252 = (

let uu____3253 = (

let uu____3260 = (subst' s t0)
in (

let uu____3263 = (

let uu____3264 = (

let uu____3273 = (subst' s t1)
in ((m1), (m2), (uu____3273)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____3264))
in ((uu____3260), (uu____3263))))
in FStar_Syntax_Syntax.Tm_meta (uu____3253))
in (mk1 uu____3252))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____3288 = (

let uu____3289 = (

let uu____3296 = (subst' s tm)
in ((uu____3296), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____3289))
in (mk1 uu____3288))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted (subst' s) qi)
in (mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi1))))))
end)
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____3310 = (

let uu____3311 = (

let uu____3318 = (subst' s t1)
in ((uu____3318), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____3311))
in (mk1 uu____3310))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (try_read_memo t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s), memo) -> begin
((

let uu____3381 = (

let uu____3386 = (push_subst s t')
in FStar_Pervasives_Native.Some (uu____3386))
in (FStar_ST.op_Colon_Equals memo uu____3381));
(compress t1);
)
end
| uu____3494 -> begin
(

let uu____3495 = (force_uvar t1)
in (match (uu____3495) with
| (t', forced) -> begin
(match (t'.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____3508) -> begin
(compress t')
end
| uu____3533 -> begin
t'
end)
end))
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (

let uu____3560 = (

let uu____3561 = (

let uu____3564 = (

let uu____3565 = (FStar_Range.use_range r)
in (FStar_Range.set_def_range r uu____3565))
in FStar_Pervasives_Native.Some (uu____3564))
in (([]), (uu____3561)))
in (subst' uu____3560 t)))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (FStar_Pervasives_Native.None)) t))


let closing_subst : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun bs -> (

let uu____3599 = (FStar_List.fold_right (fun uu____3622 uu____3623 -> (match (((uu____3622), (uu____3623))) with
| ((x, uu____3651), (subst1, n1)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n1))))::subst1), ((n1 + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____3599 FStar_Pervasives_Native.fst)))


let open_binders' : 'Auu____3684 . (FStar_Syntax_Syntax.bv * 'Auu____3684) Prims.list  ->  ((FStar_Syntax_Syntax.bv * 'Auu____3684) Prims.list * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun bs -> (

let rec aux = (fun bs1 o -> (match (bs1) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___60_3790 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____3791 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___60_3790.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___60_3790.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3791}))
in (

let o1 = (

let uu____3797 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____3797)
in (

let uu____3800 = (aux bs' o1)
in (match (uu____3800) with
| (bs'1, o2) -> begin
(((((x'), (imp)))::bs'1), (o2))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____3858 = (open_binders' bs)
in (FStar_Pervasives_Native.fst uu____3858)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____3891 = (open_binders' bs)
in (match (uu____3891) with
| (bs', opening) -> begin
(

let uu____3928 = (subst opening t)
in ((bs'), (uu____3928), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____3947 = (open_term' bs t)
in (match (uu____3947) with
| (b, t1, uu____3960) -> begin
((b), (t1))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____3971 = (open_binders' bs)
in (match (uu____3971) with
| (bs', opening) -> begin
(

let uu____4006 = (subst_comp opening t)
in ((bs'), (uu____4006)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec open_pat_aux = (fun sub1 renaming p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4086) -> begin
((p1), (sub1), (renaming))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4115 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4207 uu____4208 -> (match (((uu____4207), (uu____4208))) with
| ((pats1, sub2, renaming1), (p2, imp)) -> begin
(

let uu____4356 = (open_pat_aux sub2 renaming1 p2)
in (match (uu____4356) with
| (p3, sub3, renaming2) -> begin
(((((p3), (imp)))::pats1), (sub3), (renaming2))
end))
end)) (([]), (sub1), (renaming))))
in (match (uu____4115) with
| (pats1, sub2, renaming1) -> begin
(((

let uu___61_4526 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___61_4526.FStar_Syntax_Syntax.p})), (sub2), (renaming1))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___62_4545 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4546 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___62_4545.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___62_4545.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4546}))
in (

let sub2 = (

let uu____4552 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4552)
in (((

let uu___63_4566 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.p = uu___63_4566.FStar_Syntax_Syntax.p})), (sub2), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___64_4575 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4576 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___64_4575.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___64_4575.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4576}))
in (

let sub2 = (

let uu____4582 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4582)
in (((

let uu___65_4596 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.p = uu___65_4596.FStar_Syntax_Syntax.p})), (sub2), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___66_4610 = x
in (

let uu____4611 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___66_4610.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___66_4610.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4611}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___67_4626 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___67_4626.FStar_Syntax_Syntax.p})), (sub1), (renaming))))
end))
in (

let uu____4629 = (open_pat_aux [] [] p)
in (match (uu____4629) with
| (p1, sub1, uu____4656) -> begin
((p1), (sub1))
end))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____4683 -> (match (uu____4683) with
| (p, wopt, e) -> begin
(

let uu____4703 = (open_pat p)
in (match (uu____4703) with
| (p1, opening) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____4722 = (subst opening w)
in FStar_Pervasives_Native.Some (uu____4722))
end)
in (

let e1 = (subst opening e)
in ((p1), (wopt1), (e1))))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____4732 = (closing_subst bs)
in (subst uu____4732 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____4741 = (closing_subst bs)
in (subst_comp uu____4741 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs1 -> (match (bs1) with
| [] -> begin
[]
end
| ((x, imp))::tl1 -> begin
(

let x1 = (

let uu___68_4792 = x
in (

let uu____4793 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___68_4792.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___68_4792.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4793}))
in (

let s' = (

let uu____4799 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____4799)
in (

let uu____4802 = (aux s' tl1)
in (((x1), (imp)))::uu____4802)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____4824 -> (

let uu____4825 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (subst_comp s uu____4825))))))


let close_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4872) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4895 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4961 uu____4962 -> (match (((uu____4961), (uu____4962))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____5065 = (aux sub2 p2)
in (match (uu____5065) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4895) with
| (pats1, sub2) -> begin
(((

let uu___69_5167 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___69_5167.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___70_5186 = x
in (

let uu____5187 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___70_5186.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___70_5186.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5187}))
in (

let sub2 = (

let uu____5193 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5193)
in (((

let uu___71_5201 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___71_5201.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___72_5206 = x
in (

let uu____5207 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___72_5206.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___72_5206.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5207}))
in (

let sub2 = (

let uu____5213 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5213)
in (((

let uu___73_5221 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___73_5221.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___74_5231 = x
in (

let uu____5232 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___74_5231.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___74_5231.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5232}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___75_5241 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___75_5241.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____5246 -> (match (uu____5246) with
| (p, wopt, e) -> begin
(

let uu____5266 = (close_pat p)
in (match (uu____5266) with
| (p1, closing) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____5297 = (subst closing w)
in FStar_Pervasives_Native.Some (uu____5297))
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

let uu____5352 = (univ_var_opening us)
in (match (uu____5352) with
| (s, us') -> begin
(

let t1 = (subst s t)
in ((us'), (t1)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____5392 = (univ_var_opening us)
in (match (uu____5392) with
| (s, us') -> begin
(

let uu____5415 = (subst_comp s c)
in ((us'), (uu____5415)))
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

let uu____5459 = (

let uu____5470 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5470) with
| true -> begin
(((Prims.parse_int "0")), (lbs), ([]))
end
| uu____5485 -> begin
(FStar_List.fold_right (fun lb uu____5503 -> (match (uu____5503) with
| (i, lbs1, out) -> begin
(

let x = (

let uu____5536 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____5536))
in (((i + (Prims.parse_int "1"))), (((

let uu___76_5542 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___76_5542.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___76_5542.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___76_5542.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___76_5542.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___76_5542.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___76_5542.FStar_Syntax_Syntax.lbpos}))::lbs1), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
end))
in (match (uu____5459) with
| (n_let_recs, lbs1, let_rec_opening) -> begin
(

let lbs2 = (FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let uu____5580 = (FStar_List.fold_right (fun u uu____5608 -> (match (uu____5608) with
| (i, us, out) -> begin
(

let u1 = (FStar_Syntax_Syntax.new_univ_name FStar_Pervasives_Native.None)
in (((i + (Prims.parse_int "1"))), ((u1)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u1)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____5580) with
| (uu____5649, us, u_let_rec_opening) -> begin
(

let uu___77_5660 = lb
in (

let uu____5661 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____5664 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___77_5660.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu____5661; FStar_Syntax_Syntax.lbeff = uu___77_5660.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5664; FStar_Syntax_Syntax.lbattrs = uu___77_5660.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___77_5660.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_opening t)
in ((lbs2), (t1))))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____5686 = (

let uu____5693 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5693) with
| true -> begin
(((Prims.parse_int "0")), ([]))
end
| uu____5702 -> begin
(FStar_List.fold_right (fun lb uu____5715 -> (match (uu____5715) with
| (i, out) -> begin
(

let uu____5734 = (

let uu____5737 = (

let uu____5738 = (

let uu____5743 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____5743), (i)))
in FStar_Syntax_Syntax.NM (uu____5738))
in (uu____5737)::out)
in (((i + (Prims.parse_int "1"))), (uu____5734)))
end)) lbs (((Prims.parse_int "0")), ([])))
end))
in (match (uu____5686) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____5775 = (FStar_List.fold_right (fun u uu____5793 -> (match (uu____5793) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____5775) with
| (uu____5816, u_let_rec_closing) -> begin
(

let uu___78_5822 = lb
in (

let uu____5823 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____5826 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___78_5822.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___78_5822.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____5823; FStar_Syntax_Syntax.lbeff = uu___78_5822.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5826; FStar_Syntax_Syntax.lbattrs = uu___78_5822.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___78_5822.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_closing t)
in ((lbs1), (t1))))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____5837 -> (match (uu____5837) with
| (us, t) -> begin
(

let n1 = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____5862 -> (match (uu____5862) with
| (x, uu____5868) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n1 - i)))))
end)) binders)
in (

let t1 = (subst s t)
in ((us), (t1))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____5883 -> (match (uu____5883) with
| (us', t) -> begin
(

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n1 - i)))))) us)
in (

let uu____5905 = (subst s t)
in ((us'), (uu____5905))))))
end))


let subst_tscheme : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun s uu____5915 -> (match (uu____5915) with
| (us, t) -> begin
(

let s1 = (shift_subst (FStar_List.length us) s)
in (

let uu____5925 = (subst s1 t)
in ((us), (uu____5925))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n1 = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____5947 -> (match (uu____5947) with
| (x, uu____5953) -> begin
FStar_Syntax_Syntax.DB ((((n1 - i)), (x)))
end))))))


let closing_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (closing_subst bs))




