
open Prims
open FStar_Pervasives

let subst_to_string : 'Auu____5 . (FStar_Syntax_Syntax.bv * 'Auu____5) Prims.list  ->  Prims.string = (fun s -> (

let uu____24 = (FStar_All.pipe_right s (FStar_List.map (fun uu____45 -> (match (uu____45) with
| (b, uu____52) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right uu____24 (FStar_String.concat ", "))))


let rec apply_until_some : 'Auu____67 'Auu____68 . ('Auu____67  ->  'Auu____68 FStar_Pervasives_Native.option)  ->  'Auu____67 Prims.list  ->  ('Auu____67 Prims.list * 'Auu____68) FStar_Pervasives_Native.option = (fun f s -> (match (s) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (s0)::rest -> begin
(

let uu____110 = (f s0)
in (match (uu____110) with
| FStar_Pervasives_Native.None -> begin
(apply_until_some f rest)
end
| FStar_Pervasives_Native.Some (st) -> begin
FStar_Pervasives_Native.Some (((rest), (st)))
end))
end))


let map_some_curry : 'Auu____143 'Auu____144 'Auu____145 . ('Auu____143  ->  'Auu____144  ->  'Auu____145)  ->  'Auu____145  ->  ('Auu____143 * 'Auu____144) FStar_Pervasives_Native.option  ->  'Auu____145 = (fun f x uu___96_172 -> (match (uu___96_172) with
| FStar_Pervasives_Native.None -> begin
x
end
| FStar_Pervasives_Native.Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map : 'Auu____208 'Auu____209 'Auu____210 . ('Auu____208  ->  'Auu____209 FStar_Pervasives_Native.option)  ->  'Auu____208 Prims.list  ->  ('Auu____208 Prims.list  ->  'Auu____209  ->  'Auu____210)  ->  'Auu____210  ->  'Auu____210 = (fun f s g t -> (

let uu____258 = (apply_until_some f s)
in (FStar_All.pipe_right uu____258 (map_some_curry g t))))


let compose_subst : 'Auu____284 . ('Auu____284 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  ('Auu____284 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  ('Auu____284 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) = (fun s1 s2 -> (

let s = (FStar_List.append (FStar_Pervasives_Native.fst s1) (FStar_Pervasives_Native.fst s2))
in (

let ropt = (match ((FStar_Pervasives_Native.snd s2)) with
| FStar_Syntax_Syntax.SomeUseRange (uu____335) -> begin
(FStar_Pervasives_Native.snd s2)
end
| uu____338 -> begin
(FStar_Pervasives_Native.snd s1)
end)
in ((s), (ropt)))))


let delay : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.term = (fun t s -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t'), ((compose_subst s' s))) t.FStar_Syntax_Syntax.pos)
end
| uu____421 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t), (s)) t.FStar_Syntax_Syntax.pos)
end))


let rec force_uvar' : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar ({FStar_Syntax_Syntax.ctx_uvar_head = uv; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____447; FStar_Syntax_Syntax.ctx_uvar_binders = uu____448; FStar_Syntax_Syntax.ctx_uvar_typ = uu____449; FStar_Syntax_Syntax.ctx_uvar_reason = uu____450; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____451; FStar_Syntax_Syntax.ctx_uvar_range = uu____452; FStar_Syntax_Syntax.ctx_uvar_meta = uu____453}, s) -> begin
(

let uu____502 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____502) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____513 = (

let uu____516 = (

let uu____524 = (delay t' s)
in (force_uvar' uu____524))
in (FStar_Pervasives_Native.fst uu____516))
in ((uu____513), (true)))
end
| uu____534 -> begin
((t), (false))
end))
end
| uu____541 -> begin
((t), (false))
end))


let force_uvar : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (

let uu____563 = (force_uvar' t)
in (match (uu____563) with
| (t', forced) -> begin
(match ((not (forced))) with
| true -> begin
((t), (forced))
end
| uu____597 -> begin
(

let uu____599 = (delay t' (([]), (FStar_Syntax_Syntax.SomeUseRange (t.FStar_Syntax_Syntax.pos))))
in ((uu____599), (forced)))
end)
end)))


let rec try_read_memo_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(

let uu____673 = (FStar_ST.op_Bang m)
in (match (uu____673) with
| FStar_Pervasives_Native.None -> begin
((t), (false))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____745 = (try_read_memo_aux t')
in (match (uu____745) with
| (t'1, shorten) -> begin
((match (shorten) with
| true -> begin
(FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some (t'1)))
end
| uu____821 -> begin
()
end);
((t'1), (true));
)
end))
end))
end
| uu____827 -> begin
((t), (false))
end))


let try_read_memo : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____844 = (try_read_memo_aux t)
in (FStar_Pervasives_Native.fst uu____844)))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(

let uu____870 = (FStar_Syntax_Unionfind.univ_find u')
in (match (uu____870) with
| FStar_Pervasives_Native.Some (u1) -> begin
(compress_univ u1)
end
| uu____874 -> begin
u
end))
end
| uu____877 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___97_899 -> (match (uu___97_899) with
| FStar_Syntax_Syntax.DB (i, x) when (Prims.op_Equality i a.FStar_Syntax_Syntax.index) -> begin
(

let uu____907 = (

let uu____908 = (

let uu____909 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x uu____909))
in (FStar_Syntax_Syntax.bv_to_name uu____908))
in FStar_Pervasives_Native.Some (uu____907))
end
| uu____910 -> begin
FStar_Pervasives_Native.None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___98_936 -> (match (uu___98_936) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____945 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___104_950 = a
in {FStar_Syntax_Syntax.ppname = uu___104_950.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___104_950.FStar_Syntax_Syntax.sort}))
in FStar_Pervasives_Native.Some (uu____945))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____961 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___99_986 -> (match (uu___99_986) with
| FStar_Syntax_Syntax.UN (y, t) when (Prims.op_Equality x y) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____994 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___100_1015 -> (match (uu___100_1015) with
| FStar_Syntax_Syntax.UD (y, i) when (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____1023 -> begin
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
| FStar_Syntax_Syntax.U_unif (uu____1051) -> begin
u1
end
| FStar_Syntax_Syntax.U_succ (u2) -> begin
(

let uu____1061 = (subst_univ s u2)
in FStar_Syntax_Syntax.U_succ (uu____1061))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1065 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (uu____1065))
end)))


let tag_with_range : 'Auu____1075 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ('Auu____1075 * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Syntax_Syntax.NoUseRange -> begin
t
end
| FStar_Syntax_Syntax.SomeUseRange (r) -> begin
(

let uu____1101 = (

let uu____1103 = (FStar_Range.use_range t.FStar_Syntax_Syntax.pos)
in (

let uu____1104 = (FStar_Range.use_range r)
in (FStar_Range.rng_included uu____1103 uu____1104)))
in (match (uu____1101) with
| true -> begin
t
end
| uu____1108 -> begin
(

let r1 = (

let uu____1111 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1111))
in (

let t' = (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____1114 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_bvar (uu____1114))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____1116 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_name (uu____1116))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v1 = (

let uu___105_1122 = fv.FStar_Syntax_Syntax.fv_name
in (

let uu____1123 = (FStar_Ident.set_lid_range l r1)
in {FStar_Syntax_Syntax.v = uu____1123; FStar_Syntax_Syntax.p = uu___105_1122.FStar_Syntax_Syntax.p}))
in (

let fv1 = (

let uu___106_1125 = fv
in {FStar_Syntax_Syntax.fv_name = v1; FStar_Syntax_Syntax.fv_delta = uu___106_1125.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___106_1125.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv1))))
end
| t' -> begin
t'
end)
in (

let uu___107_1127 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___107_1127.FStar_Syntax_Syntax.vars})))
end))
end))


let tag_lid_with_range : 'Auu____1137 . FStar_Ident.lident  ->  ('Auu____1137 * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Ident.lident = (fun l s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Syntax_Syntax.NoUseRange -> begin
l
end
| FStar_Syntax_Syntax.SomeUseRange (r) -> begin
(

let uu____1157 = (

let uu____1159 = (

let uu____1160 = (FStar_Ident.range_of_lid l)
in (FStar_Range.use_range uu____1160))
in (

let uu____1161 = (FStar_Range.use_range r)
in (FStar_Range.rng_included uu____1159 uu____1161)))
in (match (uu____1157) with
| true -> begin
l
end
| uu____1163 -> begin
(

let uu____1165 = (

let uu____1166 = (FStar_Ident.range_of_lid l)
in (

let uu____1167 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range uu____1166 uu____1167)))
in (FStar_Ident.set_lid_range l uu____1165))
end))
end))


let mk_range : FStar_Range.range  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Range.range = (fun r s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Syntax_Syntax.NoUseRange -> begin
r
end
| FStar_Syntax_Syntax.SomeUseRange (r') -> begin
(

let uu____1184 = (

let uu____1186 = (FStar_Range.use_range r)
in (

let uu____1187 = (FStar_Range.use_range r')
in (FStar_Range.rng_included uu____1186 uu____1187)))
in (match (uu____1184) with
| true -> begin
r
end
| uu____1189 -> begin
(

let uu____1191 = (FStar_Range.use_range r')
in (FStar_Range.set_use_range r uu____1191))
end))
end))


let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let subst_tail = (fun tl1 -> (subst' ((tl1), ((FStar_Pervasives_Native.snd s)))))
in (match (s) with
| ([], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| (([])::[], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| uu____1312 -> begin
(

let t0 = (try_read_memo t)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1320) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1325) -> begin
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

let uu____1394 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (

let uu____1395 = (

let uu____1402 = (

let uu____1403 = (subst_univ (FStar_Pervasives_Native.fst s) u)
in FStar_Syntax_Syntax.Tm_type (uu____1403))
in (FStar_Syntax_Syntax.mk uu____1402))
in (uu____1395 FStar_Pervasives_Native.None uu____1394)))
end
| uu____1411 -> begin
(

let uu____1412 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed ((t0), (s)) uu____1412))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___101_1424 -> (match (uu___101_1424) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(

let uu____1428 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (uu____1428))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| ([], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| (([])::[], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| uu____1456 -> begin
(

let uu___108_1465 = t
in (

let uu____1466 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____1471 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____1476 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____1479 = (FStar_List.map (fun uu____1507 -> (match (uu____1507) with
| (t1, imp) -> begin
(

let uu____1526 = (subst' s t1)
in (

let uu____1527 = (subst_imp' s imp)
in ((uu____1526), (uu____1527))))
end)) t.FStar_Syntax_Syntax.effect_args)
in (

let uu____1532 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu____1466; FStar_Syntax_Syntax.effect_name = uu____1471; FStar_Syntax_Syntax.result_typ = uu____1476; FStar_Syntax_Syntax.effect_args = uu____1479; FStar_Syntax_Syntax.flags = uu____1532}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| (([])::[], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| uu____1563 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uopt) -> begin
(

let uu____1584 = (subst' s t1)
in (

let uu____1585 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____1584 uu____1585)))
end
| FStar_Syntax_Syntax.GTotal (t1, uopt) -> begin
(

let uu____1602 = (subst' s t1)
in (

let uu____1603 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1602 uu____1603)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1611 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp uu____1611))
end)
end))
and subst_imp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun s i -> (match (i) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____1629 = (

let uu____1630 = (subst' s t)
in FStar_Syntax_Syntax.Meta (uu____1630))
in FStar_Pervasives_Native.Some (uu____1629))
end
| i1 -> begin
i1
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
| FStar_Syntax_Syntax.NT (uu____1669) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n1 s -> (FStar_List.map (shift n1) s))


let shift_subst' : 'Auu____1696 . Prims.int  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1696)  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1696) = (fun n1 s -> (

let uu____1727 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (shift_subst n1)))
in ((uu____1727), ((FStar_Pervasives_Native.snd s)))))


let subst_binder' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun s uu____1770 -> (match (uu____1770) with
| (x, imp) -> begin
(

let uu____1797 = (

let uu___109_1798 = x
in (

let uu____1799 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___109_1798.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___109_1798.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1799}))
in (

let uu____1802 = (subst_imp' s imp)
in ((uu____1797), (uu____1802))))
end))


let subst_binders' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1906 -> begin
(

let uu____1908 = (shift_subst' i s)
in (subst_binder' uu____1908 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) bs))


let subst_arg' : 'Auu____1947 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term * 'Auu____1947)  ->  (FStar_Syntax_Syntax.term * 'Auu____1947) = (fun s uu____1965 -> (match (uu____1965) with
| (t, imp) -> begin
(

let uu____1972 = (subst' s t)
in ((uu____1972), (imp)))
end))


let subst_args' : 'Auu____1979 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term * 'Auu____1979) Prims.list  ->  (FStar_Syntax_Syntax.term * 'Auu____1979) Prims.list = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____2073) -> begin
((p1), (n1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2095 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____2157 uu____2158 -> (match (((uu____2157), (uu____2158))) with
| ((pats1, n2), (p2, imp)) -> begin
(

let uu____2254 = (aux n2 p2)
in (match (uu____2254) with
| (p3, m) -> begin
(((((p3), (imp)))::pats1), (m))
end))
end)) (([]), (n1))))
in (match (uu____2095) with
| (pats1, n2) -> begin
(((

let uu___110_2328 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___110_2328.FStar_Syntax_Syntax.p})), (n2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___111_2354 = x
in (

let uu____2355 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___111_2354.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___111_2354.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2355}))
in (((

let uu___112_2360 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___112_2360.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___113_2373 = x
in (

let uu____2374 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___113_2373.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___113_2373.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2374}))
in (((

let uu___114_2379 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___114_2379.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___115_2397 = x
in (

let uu____2398 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___115_2397.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_2397.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2398}))
in (

let t01 = (subst' s1 t0)
in (((

let uu___116_2404 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___116_2404.FStar_Syntax_Syntax.p})), (n1)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s lopt -> (match (lopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____2430 = (

let uu___117_2431 = rc
in (

let uu____2432 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (subst' s))
in {FStar_Syntax_Syntax.residual_effect = uu___117_2431.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____2432; FStar_Syntax_Syntax.residual_flags = uu___117_2431.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____2430))
end))


let compose_uvar_subst : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts = (fun u s0 s -> (

let should_retain = (fun x -> (FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders (FStar_Util.for_some (fun uu____2482 -> (match (uu____2482) with
| (x', uu____2491) -> begin
(FStar_Syntax_Syntax.bv_eq x x')
end)))))
in (

let rec aux = (fun uu___103_2507 -> (match (uu___103_2507) with
| [] -> begin
[]
end
| (hd_subst)::rest -> begin
(

let hd1 = (FStar_All.pipe_right hd_subst (FStar_List.collect (fun uu___102_2538 -> (match (uu___102_2538) with
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____2547 = (should_retain x)
in (match (uu____2547) with
| true -> begin
(

let uu____2552 = (

let uu____2553 = (

let uu____2560 = (delay t ((rest), (FStar_Syntax_Syntax.NoUseRange)))
in ((x), (uu____2560)))
in FStar_Syntax_Syntax.NT (uu____2553))
in (uu____2552)::[])
end
| uu____2569 -> begin
[]
end))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____2575 = (should_retain x)
in (match (uu____2575) with
| true -> begin
(

let x_i = (FStar_Syntax_Syntax.bv_to_tm (

let uu___118_2583 = x
in {FStar_Syntax_Syntax.ppname = uu___118_2583.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___118_2583.FStar_Syntax_Syntax.sort}))
in (

let t = (subst' ((rest), (FStar_Syntax_Syntax.NoUseRange)) x_i)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x_j) -> begin
(FStar_Syntax_Syntax.NM (((x), (x_j.FStar_Syntax_Syntax.index))))::[]
end
| uu____2593 -> begin
(FStar_Syntax_Syntax.NT (((x), (t))))::[]
end)))
end
| uu____2596 -> begin
[]
end))
end
| uu____2598 -> begin
[]
end))))
in (

let uu____2599 = (aux rest)
in (FStar_List.append hd1 uu____2599)))
end))
in (

let uu____2602 = (aux (FStar_List.append (FStar_Pervasives_Native.fst s0) (FStar_Pervasives_Native.fst s)))
in (match (uu____2602) with
| [] -> begin
(([]), ((FStar_Pervasives_Native.snd s)))
end
| s' -> begin
(((s')::[]), ((FStar_Pervasives_Native.snd s)))
end)))))


let rec push_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk1 = (fun t' -> (

let uu____2665 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2665)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2668) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(match (i.FStar_Syntax_Syntax.lkind) with
| FStar_Syntax_Syntax.Lazy_embedding (uu____2697) -> begin
(

let t1 = (

let uu____2707 = (

let uu____2716 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____2716))
in (uu____2707 i.FStar_Syntax_Syntax.lkind i))
in (push_subst s t1))
end
| uu____2766 -> begin
t
end)
end
| FStar_Syntax_Syntax.Tm_constant (uu____2767) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2772) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_uvar (uv, s0) -> begin
(

let uu____2799 = (FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____2799) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2804 = (

let uu___119_2807 = t
in (

let uu____2810 = (

let uu____2811 = (

let uu____2824 = (compose_uvar_subst uv s0 s)
in ((uv), (uu____2824)))
in FStar_Syntax_Syntax.Tm_uvar (uu____2811))
in {FStar_Syntax_Syntax.n = uu____2810; FStar_Syntax_Syntax.pos = uu___119_2807.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___119_2807.FStar_Syntax_Syntax.vars}))
in (tag_with_range uu____2804 s))
end
| FStar_Pervasives_Native.Some (t1) -> begin
(push_subst (compose_subst s0 s) t1)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____2848) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2849) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_name (uu____2850) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us1 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us)
in (

let uu____2864 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us1)
in (tag_with_range uu____2864 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(

let uu____2897 = (

let uu____2898 = (

let uu____2915 = (subst' s t0)
in (

let uu____2918 = (subst_args' s args)
in ((uu____2915), (uu____2918))))
in FStar_Syntax_Syntax.Tm_app (uu____2898))
in (mk1 uu____2897))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t1) -> begin
(

let uu____3019 = (subst' s t1)
in FStar_Util.Inl (uu____3019))
end
| FStar_Util.Inr (c) -> begin
(

let uu____3033 = (subst_comp' s c)
in FStar_Util.Inr (uu____3033))
end)
in (

let uu____3040 = (

let uu____3041 = (

let uu____3068 = (subst' s t0)
in (

let uu____3071 = (

let uu____3088 = (FStar_Util.map_opt topt (subst' s))
in ((annot1), (uu____3088)))
in ((uu____3068), (uu____3071), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____3041))
in (mk1 uu____3040)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n1 = (FStar_List.length bs)
in (

let s' = (shift_subst' n1 s)
in (

let uu____3174 = (

let uu____3175 = (

let uu____3194 = (subst_binders' s bs)
in (

let uu____3203 = (subst' s' body)
in (

let uu____3206 = (push_subst_lcomp s' lopt)
in ((uu____3194), (uu____3203), (uu____3206)))))
in FStar_Syntax_Syntax.Tm_abs (uu____3175))
in (mk1 uu____3174))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n1 = (FStar_List.length bs)
in (

let uu____3250 = (

let uu____3251 = (

let uu____3266 = (subst_binders' s bs)
in (

let uu____3275 = (

let uu____3278 = (shift_subst' n1 s)
in (subst_comp' uu____3278 comp))
in ((uu____3266), (uu____3275))))
in FStar_Syntax_Syntax.Tm_arrow (uu____3251))
in (mk1 uu____3250)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x1 = (

let uu___120_3308 = x
in (

let uu____3309 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___120_3308.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___120_3308.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3309}))
in (

let phi1 = (

let uu____3313 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____3313 phi))
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((x1), (phi1)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t01 = (subst' s t0)
in (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____3429 -> (match (uu____3429) with
| (pat, wopt, branch) -> begin
(

let uu____3459 = (subst_pat' s pat)
in (match (uu____3459) with
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

let uu____3490 = (subst' s1 w)
in FStar_Pervasives_Native.Some (uu____3490))
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

let uu____3562 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____3562) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____3567 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___121_3580 = x
in {FStar_Syntax_Syntax.ppname = uu___121_3580.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___121_3580.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr (fv)
end)
in (

let uu___122_3582 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___122_3582.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___122_3582.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd; FStar_Syntax_Syntax.lbattrs = uu___122_3582.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___122_3582.FStar_Syntax_Syntax.lbpos})))))))
in (mk1 (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs1))), (body1)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let uu____3613 = (

let uu____3614 = (

let uu____3621 = (subst' s t0)
in (

let uu____3624 = (

let uu____3625 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____3625))
in ((uu____3621), (uu____3624))))
in FStar_Syntax_Syntax.Tm_meta (uu____3614))
in (mk1 uu____3613))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) -> begin
(

let uu____3691 = (

let uu____3692 = (

let uu____3699 = (subst' s t0)
in (

let uu____3702 = (

let uu____3703 = (

let uu____3710 = (subst' s t1)
in ((m), (uu____3710)))
in FStar_Syntax_Syntax.Meta_monadic (uu____3703))
in ((uu____3699), (uu____3702))))
in FStar_Syntax_Syntax.Tm_meta (uu____3692))
in (mk1 uu____3691))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) -> begin
(

let uu____3729 = (

let uu____3730 = (

let uu____3737 = (subst' s t0)
in (

let uu____3740 = (

let uu____3741 = (

let uu____3750 = (subst' s t1)
in ((m1), (m2), (uu____3750)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____3741))
in ((uu____3737), (uu____3740))))
in FStar_Syntax_Syntax.Tm_meta (uu____3730))
in (mk1 uu____3729))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____3765 = (

let uu____3766 = (

let uu____3773 = (subst' s tm)
in ((uu____3773), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____3766))
in (mk1 uu____3765))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted (subst' s) qi)
in (mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi1))))))
end)
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____3787 = (

let uu____3788 = (

let uu____3795 = (subst' s t1)
in ((uu____3795), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____3788))
in (mk1 uu____3787))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (try_read_memo t)
in (

let uu____3809 = (force_uvar t1)
in (match (uu____3809) with
| (t2, uu____3818) -> begin
(match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s), memo) -> begin
((

let uu____3871 = (

let uu____3876 = (push_subst s t')
in FStar_Pervasives_Native.Some (uu____3876))
in (FStar_ST.op_Colon_Equals memo uu____3871));
(compress t2);
)
end
| uu____3930 -> begin
t2
end)
end))))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (

let uu____3965 = (

let uu____3966 = (

let uu____3967 = (

let uu____3968 = (FStar_Range.use_range r)
in (FStar_Range.set_def_range r uu____3968))
in FStar_Syntax_Syntax.SomeUseRange (uu____3967))
in (([]), (uu____3966)))
in (subst' uu____3965 t)))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) t))


let subst_imp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.aqual  ->  FStar_Syntax_Syntax.aqual = (fun s imp -> (subst_imp' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) imp))


let closing_subst : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun bs -> (

let uu____4029 = (FStar_List.fold_right (fun uu____4056 uu____4057 -> (match (((uu____4056), (uu____4057))) with
| ((x, uu____4092), (subst1, n1)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n1))))::subst1), ((n1 + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____4029 FStar_Pervasives_Native.fst)))


let open_binders' : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun bs -> (

let rec aux = (fun bs1 o -> (match (bs1) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___123_4250 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4251 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___123_4250.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_4250.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4251}))
in (

let imp1 = (subst_imp o imp)
in (

let o1 = (

let uu____4258 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4258)
in (

let uu____4264 = (aux bs' o1)
in (match (uu____4264) with
| (bs'1, o2) -> begin
(((((x'), (imp1)))::bs'1), (o2))
end)))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____4325 = (open_binders' bs)
in (FStar_Pervasives_Native.fst uu____4325)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____4363 = (open_binders' bs)
in (match (uu____4363) with
| (bs', opening) -> begin
(

let uu____4400 = (subst opening t)
in ((bs'), (uu____4400), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____4416 = (open_term' bs t)
in (match (uu____4416) with
| (b, t1, uu____4429) -> begin
((b), (t1))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____4445 = (open_binders' bs)
in (match (uu____4445) with
| (bs', opening) -> begin
(

let uu____4480 = (subst_comp opening t)
in ((bs'), (uu____4480)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec open_pat_aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4530) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4555 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4626 uu____4627 -> (match (((uu____4626), (uu____4627))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____4741 = (open_pat_aux sub2 p2)
in (match (uu____4741) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4555) with
| (pats1, sub2) -> begin
(((

let uu___124_4851 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___124_4851.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___125_4872 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4873 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___125_4872.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___125_4872.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4873}))
in (

let sub2 = (

let uu____4879 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4879)
in (((

let uu___126_4890 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.p = uu___126_4890.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___127_4895 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4896 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___127_4895.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___127_4895.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4896}))
in (

let sub2 = (

let uu____4902 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4902)
in (((

let uu___128_4913 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.p = uu___128_4913.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___129_4923 = x
in (

let uu____4924 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___129_4923.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___129_4923.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4924}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___130_4933 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___130_4933.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (open_pat_aux [] p)))


let open_branch' : FStar_Syntax_Syntax.branch  ->  (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t) = (fun uu____4947 -> (match (uu____4947) with
| (p, wopt, e) -> begin
(

let uu____4971 = (open_pat p)
in (match (uu____4971) with
| (p1, opening) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____5000 = (subst opening w)
in FStar_Pervasives_Native.Some (uu____5000))
end)
in (

let e1 = (subst opening e)
in ((((p1), (wopt1), (e1))), (opening))))
end))
end))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun br -> (

let uu____5020 = (open_branch' br)
in (match (uu____5020) with
| (br1, uu____5026) -> begin
br1
end)))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____5038 = (closing_subst bs)
in (subst uu____5038 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____5052 = (closing_subst bs)
in (subst_comp uu____5052 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs1 -> (match (bs1) with
| [] -> begin
[]
end
| ((x, imp))::tl1 -> begin
(

let x1 = (

let uu___131_5120 = x
in (

let uu____5121 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___131_5120.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_5120.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5121}))
in (

let imp1 = (subst_imp s imp)
in (

let s' = (

let uu____5128 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5128)
in (

let uu____5134 = (aux s' tl1)
in (((x1), (imp1)))::uu____5134))))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____5161 -> (

let uu____5162 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (subst_comp s uu____5162))))))


let close_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____5216) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____5241 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____5312 uu____5313 -> (match (((uu____5312), (uu____5313))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____5427 = (aux sub2 p2)
in (match (uu____5427) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____5241) with
| (pats1, sub2) -> begin
(((

let uu___132_5537 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___132_5537.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___133_5558 = x
in (

let uu____5559 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___133_5558.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_5558.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5559}))
in (

let sub2 = (

let uu____5565 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5565)
in (((

let uu___134_5576 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___134_5576.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___135_5581 = x
in (

let uu____5582 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___135_5581.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___135_5581.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5582}))
in (

let sub2 = (

let uu____5588 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5588)
in (((

let uu___136_5599 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___136_5599.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___137_5609 = x
in (

let uu____5610 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___137_5609.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___137_5609.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5610}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___138_5619 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___138_5619.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____5629 -> (match (uu____5629) with
| (p, wopt, e) -> begin
(

let uu____5649 = (close_pat p)
in (match (uu____5649) with
| (p1, closing) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____5686 = (subst closing w)
in FStar_Pervasives_Native.Some (uu____5686))
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

let uu____5774 = (univ_var_opening us)
in (match (uu____5774) with
| (s, us') -> begin
(

let t1 = (subst s t)
in ((us'), (t1)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____5817 = (univ_var_opening us)
in (match (uu____5817) with
| (s, us') -> begin
(

let uu____5840 = (subst_comp s c)
in ((us'), (uu____5840)))
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

let uu____5903 = (

let uu____5915 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5915) with
| true -> begin
(((Prims.parse_int "0")), (lbs), ([]))
end
| uu____5935 -> begin
(FStar_List.fold_right (fun lb uu____5955 -> (match (uu____5955) with
| (i, lbs1, out) -> begin
(

let x = (

let uu____5992 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____5992))
in (((i + (Prims.parse_int "1"))), (((

let uu___139_6000 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___139_6000.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___139_6000.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___139_6000.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___139_6000.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___139_6000.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___139_6000.FStar_Syntax_Syntax.lbpos}))::lbs1), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
end))
in (match (uu____5903) with
| (n_let_recs, lbs1, let_rec_opening) -> begin
(

let lbs2 = (FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let uu____6043 = (FStar_List.fold_right (fun u uu____6073 -> (match (uu____6073) with
| (i, us, out) -> begin
(

let u1 = (FStar_Syntax_Syntax.new_univ_name FStar_Pervasives_Native.None)
in (((i + (Prims.parse_int "1"))), ((u1)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u1)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____6043) with
| (uu____6122, us, u_let_rec_opening) -> begin
(

let uu___140_6135 = lb
in (

let uu____6136 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____6139 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___140_6135.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu____6136; FStar_Syntax_Syntax.lbeff = uu___140_6135.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____6139; FStar_Syntax_Syntax.lbattrs = uu___140_6135.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___140_6135.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_opening t)
in ((lbs2), (t1))))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____6166 = (

let uu____6174 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____6174) with
| true -> begin
(((Prims.parse_int "0")), ([]))
end
| uu____6188 -> begin
(FStar_List.fold_right (fun lb uu____6203 -> (match (uu____6203) with
| (i, out) -> begin
(

let uu____6226 = (

let uu____6229 = (

let uu____6230 = (

let uu____6236 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____6236), (i)))
in FStar_Syntax_Syntax.NM (uu____6230))
in (uu____6229)::out)
in (((i + (Prims.parse_int "1"))), (uu____6226)))
end)) lbs (((Prims.parse_int "0")), ([])))
end))
in (match (uu____6166) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____6275 = (FStar_List.fold_right (fun u uu____6295 -> (match (uu____6295) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____6275) with
| (uu____6326, u_let_rec_closing) -> begin
(

let uu___141_6334 = lb
in (

let uu____6335 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____6338 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___141_6334.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___141_6334.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____6335; FStar_Syntax_Syntax.lbeff = uu___141_6334.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____6338; FStar_Syntax_Syntax.lbattrs = uu___141_6334.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___141_6334.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_closing t)
in ((lbs1), (t1))))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____6354 -> (match (uu____6354) with
| (us, t) -> begin
(

let n1 = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____6389 -> (match (uu____6389) with
| (x, uu____6398) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n1 - i)))))
end)) binders)
in (

let t1 = (subst s t)
in ((us), (t1))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____6425 -> (match (uu____6425) with
| (us', t) -> begin
(

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n1 - i)))))) us)
in (

let uu____6455 = (subst s t)
in ((us'), (uu____6455))))))
end))


let subst_tscheme : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun s uu____6474 -> (match (uu____6474) with
| (us, t) -> begin
(

let s1 = (shift_subst (FStar_List.length us) s)
in (

let uu____6488 = (subst s1 t)
in ((us), (uu____6488))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n1 = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____6529 -> (match (uu____6529) with
| (x, uu____6538) -> begin
FStar_Syntax_Syntax.DB ((((n1 - i)), (x)))
end))))))


let closing_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (closing_subst bs))


let open_term_1 : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term) = (fun b t -> (

let uu____6565 = (open_term ((b)::[]) t)
in (match (uu____6565) with
| ((b1)::[], t1) -> begin
((b1), (t1))
end
| uu____6606 -> begin
(failwith "impossible: open_term_1")
end)))


let open_term_bvs : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun bvs t -> (

let uu____6637 = (

let uu____6642 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (open_term uu____6642 t))
in (match (uu____6637) with
| (bs, t1) -> begin
(

let uu____6657 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in ((uu____6657), (t1)))
end)))


let open_term_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun bv t -> (

let uu____6685 = (open_term_bvs ((bv)::[]) t)
in (match (uu____6685) with
| ((bv1)::[], t1) -> begin
((bv1), (t1))
end
| uu____6700 -> begin
(failwith "impossible: open_term_bv")
end)))




