
open Prims
open FStar_Pervasives

let subst_to_string : 'Auu____4 . (FStar_Syntax_Syntax.bv * 'Auu____4) Prims.list  ->  Prims.string = (fun s -> (

let uu____23 = (FStar_All.pipe_right s (FStar_List.map (fun uu____44 -> (match (uu____44) with
| (b, uu____51) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right uu____23 (FStar_String.concat ", "))))


let rec apply_until_some : 'Auu____66 'Auu____67 . ('Auu____66  ->  'Auu____67 FStar_Pervasives_Native.option)  ->  'Auu____66 Prims.list  ->  ('Auu____66 Prims.list * 'Auu____67) FStar_Pervasives_Native.option = (fun f s -> (match (s) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (s0)::rest -> begin
(

let uu____109 = (f s0)
in (match (uu____109) with
| FStar_Pervasives_Native.None -> begin
(apply_until_some f rest)
end
| FStar_Pervasives_Native.Some (st) -> begin
FStar_Pervasives_Native.Some (((rest), (st)))
end))
end))


let map_some_curry : 'Auu____142 'Auu____143 'Auu____144 . ('Auu____142  ->  'Auu____143  ->  'Auu____144)  ->  'Auu____144  ->  ('Auu____142 * 'Auu____143) FStar_Pervasives_Native.option  ->  'Auu____144 = (fun f x uu___0_171 -> (match (uu___0_171) with
| FStar_Pervasives_Native.None -> begin
x
end
| FStar_Pervasives_Native.Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map : 'Auu____207 'Auu____208 'Auu____209 . ('Auu____207  ->  'Auu____208 FStar_Pervasives_Native.option)  ->  'Auu____207 Prims.list  ->  ('Auu____207 Prims.list  ->  'Auu____208  ->  'Auu____209)  ->  'Auu____209  ->  'Auu____209 = (fun f s g t -> (

let uu____257 = (apply_until_some f s)
in (FStar_All.pipe_right uu____257 (map_some_curry g t))))


let compose_subst : 'Auu____283 . ('Auu____283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  ('Auu____283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  ('Auu____283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) = (fun s1 s2 -> (

let s = (FStar_List.append (FStar_Pervasives_Native.fst s1) (FStar_Pervasives_Native.fst s2))
in (

let ropt = (match ((FStar_Pervasives_Native.snd s2)) with
| FStar_Syntax_Syntax.SomeUseRange (uu____334) -> begin
(FStar_Pervasives_Native.snd s2)
end
| uu____337 -> begin
(FStar_Pervasives_Native.snd s1)
end)
in ((s), (ropt)))))


let delay : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.term = (fun t s -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t'), ((compose_subst s' s))) t.FStar_Syntax_Syntax.pos)
end
| uu____420 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t), (s)) t.FStar_Syntax_Syntax.pos)
end))


let rec force_uvar' : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar ({FStar_Syntax_Syntax.ctx_uvar_head = uv; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____446; FStar_Syntax_Syntax.ctx_uvar_binders = uu____447; FStar_Syntax_Syntax.ctx_uvar_typ = uu____448; FStar_Syntax_Syntax.ctx_uvar_reason = uu____449; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____450; FStar_Syntax_Syntax.ctx_uvar_range = uu____451; FStar_Syntax_Syntax.ctx_uvar_meta = uu____452}, s) -> begin
(

let uu____501 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____501) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____512 = (

let uu____515 = (

let uu____523 = (delay t' s)
in (force_uvar' uu____523))
in (FStar_Pervasives_Native.fst uu____515))
in ((uu____512), (true)))
end
| uu____533 -> begin
((t), (false))
end))
end
| uu____540 -> begin
((t), (false))
end))


let force_uvar : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (

let uu____562 = (force_uvar' t)
in (match (uu____562) with
| (t', forced) -> begin
(match ((not (forced))) with
| true -> begin
((t), (forced))
end
| uu____596 -> begin
(

let uu____598 = (delay t' (([]), (FStar_Syntax_Syntax.SomeUseRange (t.FStar_Syntax_Syntax.pos))))
in ((uu____598), (forced)))
end)
end)))


let rec try_read_memo_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(

let uu____672 = (FStar_ST.op_Bang m)
in (match (uu____672) with
| FStar_Pervasives_Native.None -> begin
((t), (false))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____722 = (try_read_memo_aux t')
in (match (uu____722) with
| (t'1, shorten) -> begin
((match (shorten) with
| true -> begin
(FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some (t'1)))
end
| uu____776 -> begin
()
end);
((t'1), (true));
)
end))
end))
end
| uu____782 -> begin
((t), (false))
end))


let try_read_memo : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____799 = (try_read_memo_aux t)
in (FStar_Pervasives_Native.fst uu____799)))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(

let uu____825 = (FStar_Syntax_Unionfind.univ_find u')
in (match (uu____825) with
| FStar_Pervasives_Native.Some (u1) -> begin
(compress_univ u1)
end
| uu____829 -> begin
u
end))
end
| uu____832 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___1_854 -> (match (uu___1_854) with
| FStar_Syntax_Syntax.DB (i, x) when (Prims.op_Equality i a.FStar_Syntax_Syntax.index) -> begin
(

let uu____862 = (

let uu____863 = (

let uu____864 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x uu____864))
in (FStar_Syntax_Syntax.bv_to_name uu____863))
in FStar_Pervasives_Native.Some (uu____862))
end
| uu____865 -> begin
FStar_Pervasives_Native.None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___2_891 -> (match (uu___2_891) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____900 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___108_905 = a
in {FStar_Syntax_Syntax.ppname = uu___108_905.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___108_905.FStar_Syntax_Syntax.sort}))
in FStar_Pervasives_Native.Some (uu____900))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____916 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___3_941 -> (match (uu___3_941) with
| FStar_Syntax_Syntax.UN (y, t) when (Prims.op_Equality x y) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____949 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___4_970 -> (match (uu___4_970) with
| FStar_Syntax_Syntax.UD (y, i) when (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____978 -> begin
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
| FStar_Syntax_Syntax.U_unif (uu____1006) -> begin
u1
end
| FStar_Syntax_Syntax.U_succ (u2) -> begin
(

let uu____1016 = (subst_univ s u2)
in FStar_Syntax_Syntax.U_succ (uu____1016))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1020 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (uu____1020))
end)))


let tag_with_range : 'Auu____1030 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ('Auu____1030 * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Syntax_Syntax.NoUseRange -> begin
t
end
| FStar_Syntax_Syntax.SomeUseRange (r) -> begin
(

let uu____1056 = (

let uu____1058 = (FStar_Range.use_range t.FStar_Syntax_Syntax.pos)
in (

let uu____1059 = (FStar_Range.use_range r)
in (FStar_Range.rng_included uu____1058 uu____1059)))
in (match (uu____1056) with
| true -> begin
t
end
| uu____1063 -> begin
(

let r1 = (

let uu____1066 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1066))
in (

let t' = (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____1069 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_bvar (uu____1069))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____1071 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_name (uu____1071))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v1 = (

let uu___160_1077 = fv.FStar_Syntax_Syntax.fv_name
in (

let uu____1078 = (FStar_Ident.set_lid_range l r1)
in {FStar_Syntax_Syntax.v = uu____1078; FStar_Syntax_Syntax.p = uu___160_1077.FStar_Syntax_Syntax.p}))
in (

let fv1 = (

let uu___163_1080 = fv
in {FStar_Syntax_Syntax.fv_name = v1; FStar_Syntax_Syntax.fv_delta = uu___163_1080.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___163_1080.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv1))))
end
| t' -> begin
t'
end)
in (

let uu___168_1082 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___168_1082.FStar_Syntax_Syntax.vars})))
end))
end))


let tag_lid_with_range : 'Auu____1092 . FStar_Ident.lident  ->  ('Auu____1092 * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Ident.lident = (fun l s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Syntax_Syntax.NoUseRange -> begin
l
end
| FStar_Syntax_Syntax.SomeUseRange (r) -> begin
(

let uu____1112 = (

let uu____1114 = (

let uu____1115 = (FStar_Ident.range_of_lid l)
in (FStar_Range.use_range uu____1115))
in (

let uu____1116 = (FStar_Range.use_range r)
in (FStar_Range.rng_included uu____1114 uu____1116)))
in (match (uu____1112) with
| true -> begin
l
end
| uu____1118 -> begin
(

let uu____1120 = (

let uu____1121 = (FStar_Ident.range_of_lid l)
in (

let uu____1122 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range uu____1121 uu____1122)))
in (FStar_Ident.set_lid_range l uu____1120))
end))
end))


let mk_range : FStar_Range.range  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Range.range = (fun r s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Syntax_Syntax.NoUseRange -> begin
r
end
| FStar_Syntax_Syntax.SomeUseRange (r') -> begin
(

let uu____1139 = (

let uu____1141 = (FStar_Range.use_range r)
in (

let uu____1142 = (FStar_Range.use_range r')
in (FStar_Range.rng_included uu____1141 uu____1142)))
in (match (uu____1139) with
| true -> begin
r
end
| uu____1144 -> begin
(

let uu____1146 = (FStar_Range.use_range r')
in (FStar_Range.set_use_range r uu____1146))
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
| uu____1267 -> begin
(

let t0 = (try_read_memo t)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1275) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1280) -> begin
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

let uu____1349 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (

let uu____1350 = (

let uu____1357 = (

let uu____1358 = (subst_univ (FStar_Pervasives_Native.fst s) u)
in FStar_Syntax_Syntax.Tm_type (uu____1358))
in (FStar_Syntax_Syntax.mk uu____1357))
in (uu____1350 FStar_Pervasives_Native.None uu____1349)))
end
| uu____1363 -> begin
(

let uu____1364 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed ((t0), (s)) uu____1364))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___5_1376 -> (match (uu___5_1376) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(

let uu____1380 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (uu____1380))
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
| uu____1408 -> begin
(

let uu___229_1417 = t
in (

let uu____1418 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____1423 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____1428 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____1431 = (FStar_List.map (fun uu____1459 -> (match (uu____1459) with
| (t1, imp) -> begin
(

let uu____1478 = (subst' s t1)
in (

let uu____1479 = (subst_imp' s imp)
in ((uu____1478), (uu____1479))))
end)) t.FStar_Syntax_Syntax.effect_args)
in (

let uu____1484 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu____1418; FStar_Syntax_Syntax.effect_name = uu____1423; FStar_Syntax_Syntax.result_typ = uu____1428; FStar_Syntax_Syntax.effect_args = uu____1431; FStar_Syntax_Syntax.flags = uu____1484}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| (([])::[], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| uu____1515 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uopt) -> begin
(

let uu____1536 = (subst' s t1)
in (

let uu____1537 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____1536 uu____1537)))
end
| FStar_Syntax_Syntax.GTotal (t1, uopt) -> begin
(

let uu____1554 = (subst' s t1)
in (

let uu____1555 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1554 uu____1555)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1563 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp uu____1563))
end)
end))
and subst_imp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun s i -> (match (i) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____1581 = (

let uu____1582 = (subst' s t)
in FStar_Syntax_Syntax.Meta (uu____1582))
in FStar_Pervasives_Native.Some (uu____1581))
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
| FStar_Syntax_Syntax.NT (uu____1621) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n1 s -> (FStar_List.map (shift n1) s))


let shift_subst' : 'Auu____1648 . Prims.int  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1648)  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1648) = (fun n1 s -> (

let uu____1679 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (shift_subst n1)))
in ((uu____1679), ((FStar_Pervasives_Native.snd s)))))


let subst_binder' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun s uu____1722 -> (match (uu____1722) with
| (x, imp) -> begin
(

let uu____1749 = (

let uu___288_1750 = x
in (

let uu____1751 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___288_1750.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___288_1750.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1751}))
in (

let uu____1754 = (subst_imp' s imp)
in ((uu____1749), (uu____1754))))
end))


let subst_binders' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1858 -> begin
(

let uu____1860 = (shift_subst' i s)
in (subst_binder' uu____1860 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) bs))


let subst_arg' : 'Auu____1899 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term * 'Auu____1899)  ->  (FStar_Syntax_Syntax.term * 'Auu____1899) = (fun s uu____1917 -> (match (uu____1917) with
| (t, imp) -> begin
(

let uu____1924 = (subst' s t)
in ((uu____1924), (imp)))
end))


let subst_args' : 'Auu____1931 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term * 'Auu____1931) Prims.list  ->  (FStar_Syntax_Syntax.term * 'Auu____1931) Prims.list = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____2025) -> begin
((p1), (n1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2047 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____2109 uu____2110 -> (match (((uu____2109), (uu____2110))) with
| ((pats1, n2), (p2, imp)) -> begin
(

let uu____2206 = (aux n2 p2)
in (match (uu____2206) with
| (p3, m) -> begin
(((((p3), (imp)))::pats1), (m))
end))
end)) (([]), (n1))))
in (match (uu____2047) with
| (pats1, n2) -> begin
(((

let uu___325_2280 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___325_2280.FStar_Syntax_Syntax.p})), (n2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___330_2306 = x
in (

let uu____2307 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___330_2306.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___330_2306.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2307}))
in (((

let uu___333_2312 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___333_2312.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___338_2325 = x
in (

let uu____2326 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___338_2325.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___338_2325.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2326}))
in (((

let uu___341_2331 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___341_2331.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___348_2349 = x
in (

let uu____2350 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___348_2349.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___348_2349.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2350}))
in (

let t01 = (subst' s1 t0)
in (((

let uu___352_2356 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___352_2356.FStar_Syntax_Syntax.p})), (n1)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s lopt -> (match (lopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____2382 = (

let uu___359_2383 = rc
in (

let uu____2384 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (subst' s))
in {FStar_Syntax_Syntax.residual_effect = uu___359_2383.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____2384; FStar_Syntax_Syntax.residual_flags = uu___359_2383.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____2382))
end))


let compose_uvar_subst : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts = (fun u s0 s -> (

let should_retain = (fun x -> (FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders (FStar_Util.for_some (fun uu____2434 -> (match (uu____2434) with
| (x', uu____2443) -> begin
(FStar_Syntax_Syntax.bv_eq x x')
end)))))
in (

let rec aux = (fun uu___7_2459 -> (match (uu___7_2459) with
| [] -> begin
[]
end
| (hd_subst)::rest -> begin
(

let hd1 = (FStar_All.pipe_right hd_subst (FStar_List.collect (fun uu___6_2490 -> (match (uu___6_2490) with
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____2499 = (should_retain x)
in (match (uu____2499) with
| true -> begin
(

let uu____2504 = (

let uu____2505 = (

let uu____2512 = (delay t ((rest), (FStar_Syntax_Syntax.NoUseRange)))
in ((x), (uu____2512)))
in FStar_Syntax_Syntax.NT (uu____2505))
in (uu____2504)::[])
end
| uu____2521 -> begin
[]
end))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____2527 = (should_retain x)
in (match (uu____2527) with
| true -> begin
(

let x_i = (FStar_Syntax_Syntax.bv_to_tm (

let uu___386_2535 = x
in {FStar_Syntax_Syntax.ppname = uu___386_2535.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___386_2535.FStar_Syntax_Syntax.sort}))
in (

let t = (subst' ((rest), (FStar_Syntax_Syntax.NoUseRange)) x_i)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x_j) -> begin
(FStar_Syntax_Syntax.NM (((x), (x_j.FStar_Syntax_Syntax.index))))::[]
end
| uu____2545 -> begin
(FStar_Syntax_Syntax.NT (((x), (t))))::[]
end)))
end
| uu____2548 -> begin
[]
end))
end
| uu____2550 -> begin
[]
end))))
in (

let uu____2551 = (aux rest)
in (FStar_List.append hd1 uu____2551)))
end))
in (

let uu____2554 = (aux (FStar_List.append (FStar_Pervasives_Native.fst s0) (FStar_Pervasives_Native.fst s)))
in (match (uu____2554) with
| [] -> begin
(([]), ((FStar_Pervasives_Native.snd s)))
end
| s' -> begin
(((s')::[]), ((FStar_Pervasives_Native.snd s)))
end)))))


let rec push_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk1 = (fun t' -> (

let uu____2617 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2617)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2620) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(match (i.FStar_Syntax_Syntax.lkind) with
| FStar_Syntax_Syntax.Lazy_embedding (uu____2649) -> begin
(

let t1 = (

let uu____2659 = (

let uu____2668 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____2668))
in (uu____2659 i.FStar_Syntax_Syntax.lkind i))
in (push_subst s t1))
end
| uu____2718 -> begin
t
end)
end
| FStar_Syntax_Syntax.Tm_constant (uu____2719) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2724) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_uvar (uv, s0) -> begin
(

let uu____2751 = (FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____2751) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2756 = (

let uu___419_2759 = t
in (

let uu____2762 = (

let uu____2763 = (

let uu____2776 = (compose_uvar_subst uv s0 s)
in ((uv), (uu____2776)))
in FStar_Syntax_Syntax.Tm_uvar (uu____2763))
in {FStar_Syntax_Syntax.n = uu____2762; FStar_Syntax_Syntax.pos = uu___419_2759.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___419_2759.FStar_Syntax_Syntax.vars}))
in (tag_with_range uu____2756 s))
end
| FStar_Pervasives_Native.Some (t1) -> begin
(push_subst (compose_subst s0 s) t1)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____2800) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2801) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_name (uu____2802) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us1 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us)
in (

let uu____2816 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us1)
in (tag_with_range uu____2816 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(

let uu____2849 = (

let uu____2850 = (

let uu____2867 = (subst' s t0)
in (

let uu____2870 = (subst_args' s args)
in ((uu____2867), (uu____2870))))
in FStar_Syntax_Syntax.Tm_app (uu____2850))
in (mk1 uu____2849))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t1) -> begin
(

let uu____2971 = (subst' s t1)
in FStar_Util.Inl (uu____2971))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2985 = (subst_comp' s c)
in FStar_Util.Inr (uu____2985))
end)
in (

let uu____2992 = (

let uu____2993 = (

let uu____3020 = (subst' s t0)
in (

let uu____3023 = (

let uu____3040 = (FStar_Util.map_opt topt (subst' s))
in ((annot1), (uu____3040)))
in ((uu____3020), (uu____3023), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2993))
in (mk1 uu____2992)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n1 = (FStar_List.length bs)
in (

let s' = (shift_subst' n1 s)
in (

let uu____3122 = (

let uu____3123 = (

let uu____3142 = (subst_binders' s bs)
in (

let uu____3151 = (subst' s' body)
in (

let uu____3154 = (push_subst_lcomp s' lopt)
in ((uu____3142), (uu____3151), (uu____3154)))))
in FStar_Syntax_Syntax.Tm_abs (uu____3123))
in (mk1 uu____3122))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n1 = (FStar_List.length bs)
in (

let uu____3198 = (

let uu____3199 = (

let uu____3214 = (subst_binders' s bs)
in (

let uu____3223 = (

let uu____3226 = (shift_subst' n1 s)
in (subst_comp' uu____3226 comp))
in ((uu____3214), (uu____3223))))
in FStar_Syntax_Syntax.Tm_arrow (uu____3199))
in (mk1 uu____3198)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x1 = (

let uu___466_3252 = x
in (

let uu____3253 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___466_3252.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___466_3252.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3253}))
in (

let phi1 = (

let uu____3257 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____3257 phi))
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((x1), (phi1)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t01 = (subst' s t0)
in (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____3373 -> (match (uu____3373) with
| (pat, wopt, branch) -> begin
(

let uu____3403 = (subst_pat' s pat)
in (match (uu____3403) with
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

let uu____3434 = (subst' s1 w)
in FStar_Pervasives_Native.Some (uu____3434))
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

let uu____3502 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____3502) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____3507 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___504_3520 = x
in {FStar_Syntax_Syntax.ppname = uu___504_3520.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___504_3520.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr (fv)
end)
in (

let uu___509_3522 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___509_3522.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___509_3522.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd; FStar_Syntax_Syntax.lbattrs = uu___509_3522.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___509_3522.FStar_Syntax_Syntax.lbpos})))))))
in (mk1 (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs1))), (body1)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (bs, ps)) -> begin
(

let uu____3574 = (

let uu____3575 = (

let uu____3582 = (subst' s t0)
in (

let uu____3585 = (

let uu____3586 = (

let uu____3607 = (FStar_List.map (subst' s) bs)
in (

let uu____3616 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in ((uu____3607), (uu____3616))))
in FStar_Syntax_Syntax.Meta_pattern (uu____3586))
in ((uu____3582), (uu____3585))))
in FStar_Syntax_Syntax.Tm_meta (uu____3575))
in (mk1 uu____3574))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) -> begin
(

let uu____3698 = (

let uu____3699 = (

let uu____3706 = (subst' s t0)
in (

let uu____3709 = (

let uu____3710 = (

let uu____3717 = (subst' s t1)
in ((m), (uu____3717)))
in FStar_Syntax_Syntax.Meta_monadic (uu____3710))
in ((uu____3706), (uu____3709))))
in FStar_Syntax_Syntax.Tm_meta (uu____3699))
in (mk1 uu____3698))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) -> begin
(

let uu____3736 = (

let uu____3737 = (

let uu____3744 = (subst' s t0)
in (

let uu____3747 = (

let uu____3748 = (

let uu____3757 = (subst' s t1)
in ((m1), (m2), (uu____3757)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____3748))
in ((uu____3744), (uu____3747))))
in FStar_Syntax_Syntax.Tm_meta (uu____3737))
in (mk1 uu____3736))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____3772 = (

let uu____3773 = (

let uu____3780 = (subst' s tm)
in ((uu____3780), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____3773))
in (mk1 uu____3772))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted (subst' s) qi)
in (mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi1))))))
end)
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____3794 = (

let uu____3795 = (

let uu____3802 = (subst' s t1)
in ((uu____3802), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____3795))
in (mk1 uu____3794))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (try_read_memo t)
in (

let uu____3816 = (force_uvar t1)
in (match (uu____3816) with
| (t2, uu____3825) -> begin
(match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s), memo) -> begin
((

let uu____3878 = (

let uu____3883 = (push_subst s t')
in FStar_Pervasives_Native.Some (uu____3883))
in (FStar_ST.op_Colon_Equals memo uu____3878));
(compress t2);
)
end
| uu____3915 -> begin
t2
end)
end))))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (

let uu____3950 = (

let uu____3951 = (

let uu____3952 = (

let uu____3953 = (FStar_Range.use_range r)
in (FStar_Range.set_def_range r uu____3953))
in FStar_Syntax_Syntax.SomeUseRange (uu____3952))
in (([]), (uu____3951)))
in (subst' uu____3950 t)))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) t))


let subst_imp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.aqual  ->  FStar_Syntax_Syntax.aqual = (fun s imp -> (subst_imp' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) imp))


let closing_subst : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun bs -> (

let uu____4014 = (FStar_List.fold_right (fun uu____4041 uu____4042 -> (match (((uu____4041), (uu____4042))) with
| ((x, uu____4077), (subst1, n1)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n1))))::subst1), ((n1 + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____4014 FStar_Pervasives_Native.fst)))


let open_binders' : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun bs -> (

let rec aux = (fun bs1 o -> (match (bs1) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___583_4235 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4236 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___583_4235.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___583_4235.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4236}))
in (

let imp1 = (subst_imp o imp)
in (

let o1 = (

let uu____4243 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4243)
in (

let uu____4249 = (aux bs' o1)
in (match (uu____4249) with
| (bs'1, o2) -> begin
(((((x'), (imp1)))::bs'1), (o2))
end)))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____4310 = (open_binders' bs)
in (FStar_Pervasives_Native.fst uu____4310)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____4348 = (open_binders' bs)
in (match (uu____4348) with
| (bs', opening) -> begin
(

let uu____4385 = (subst opening t)
in ((bs'), (uu____4385), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____4401 = (open_term' bs t)
in (match (uu____4401) with
| (b, t1, uu____4414) -> begin
((b), (t1))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____4430 = (open_binders' bs)
in (match (uu____4430) with
| (bs', opening) -> begin
(

let uu____4465 = (subst_comp opening t)
in ((bs'), (uu____4465)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec open_pat_aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4515) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4540 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4611 uu____4612 -> (match (((uu____4611), (uu____4612))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____4726 = (open_pat_aux sub2 p2)
in (match (uu____4726) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4540) with
| (pats1, sub2) -> begin
(((

let uu___630_4836 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___630_4836.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___634_4857 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4858 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___634_4857.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___634_4857.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4858}))
in (

let sub2 = (

let uu____4864 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4864)
in (((

let uu___638_4875 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.p = uu___638_4875.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___642_4880 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4881 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___642_4880.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___642_4880.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4881}))
in (

let sub2 = (

let uu____4887 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4887)
in (((

let uu___646_4898 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.p = uu___646_4898.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___652_4908 = x
in (

let uu____4909 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___652_4908.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___652_4908.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4909}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___656_4918 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___656_4918.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (open_pat_aux [] p)))


let open_branch' : FStar_Syntax_Syntax.branch  ->  (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t) = (fun uu____4932 -> (match (uu____4932) with
| (p, wopt, e) -> begin
(

let uu____4956 = (open_pat p)
in (match (uu____4956) with
| (p1, opening) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____4985 = (subst opening w)
in FStar_Pervasives_Native.Some (uu____4985))
end)
in (

let e1 = (subst opening e)
in ((((p1), (wopt1), (e1))), (opening))))
end))
end))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun br -> (

let uu____5005 = (open_branch' br)
in (match (uu____5005) with
| (br1, uu____5011) -> begin
br1
end)))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____5023 = (closing_subst bs)
in (subst uu____5023 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____5037 = (closing_subst bs)
in (subst_comp uu____5037 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs1 -> (match (bs1) with
| [] -> begin
[]
end
| ((x, imp))::tl1 -> begin
(

let x1 = (

let uu___688_5105 = x
in (

let uu____5106 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___688_5105.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___688_5105.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5106}))
in (

let imp1 = (subst_imp s imp)
in (

let s' = (

let uu____5113 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5113)
in (

let uu____5119 = (aux s' tl1)
in (((x1), (imp1)))::uu____5119))))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____5146 -> (

let uu____5147 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (subst_comp s uu____5147))))))


let close_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____5201) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____5226 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____5297 uu____5298 -> (match (((uu____5297), (uu____5298))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____5412 = (aux sub2 p2)
in (match (uu____5412) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____5226) with
| (pats1, sub2) -> begin
(((

let uu___719_5522 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___719_5522.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___723_5543 = x
in (

let uu____5544 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___723_5543.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___723_5543.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5544}))
in (

let sub2 = (

let uu____5550 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5550)
in (((

let uu___727_5561 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___727_5561.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___731_5566 = x
in (

let uu____5567 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___731_5566.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___731_5566.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5567}))
in (

let sub2 = (

let uu____5573 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5573)
in (((

let uu___735_5584 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___735_5584.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___741_5594 = x
in (

let uu____5595 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___741_5594.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___741_5594.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5595}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___745_5604 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___745_5604.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____5614 -> (match (uu____5614) with
| (p, wopt, e) -> begin
(

let uu____5634 = (close_pat p)
in (match (uu____5634) with
| (p1, closing) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____5671 = (subst closing w)
in FStar_Pervasives_Native.Some (uu____5671))
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

let uu____5759 = (univ_var_opening us)
in (match (uu____5759) with
| (s, us') -> begin
(

let t1 = (subst s t)
in ((us'), (t1)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____5802 = (univ_var_opening us)
in (match (uu____5802) with
| (s, us') -> begin
(

let uu____5825 = (subst_comp s c)
in ((us'), (uu____5825)))
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

let uu____5888 = (

let uu____5900 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5900) with
| true -> begin
(((Prims.parse_int "0")), (lbs), ([]))
end
| uu____5920 -> begin
(FStar_List.fold_right (fun lb uu____5940 -> (match (uu____5940) with
| (i, lbs1, out) -> begin
(

let x = (

let uu____5977 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____5977))
in (((i + (Prims.parse_int "1"))), (((

let uu___797_5985 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___797_5985.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___797_5985.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___797_5985.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___797_5985.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___797_5985.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___797_5985.FStar_Syntax_Syntax.lbpos}))::lbs1), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
end))
in (match (uu____5888) with
| (n_let_recs, lbs1, let_rec_opening) -> begin
(

let lbs2 = (FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let uu____6028 = (FStar_List.fold_right (fun u uu____6058 -> (match (uu____6058) with
| (i, us, out) -> begin
(

let u1 = (FStar_Syntax_Syntax.new_univ_name FStar_Pervasives_Native.None)
in (((i + (Prims.parse_int "1"))), ((u1)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u1)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____6028) with
| (uu____6107, us, u_let_rec_opening) -> begin
(

let uu___814_6120 = lb
in (

let uu____6121 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____6124 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___814_6120.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu____6121; FStar_Syntax_Syntax.lbeff = uu___814_6120.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____6124; FStar_Syntax_Syntax.lbattrs = uu___814_6120.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___814_6120.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_opening t)
in ((lbs2), (t1))))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____6151 = (

let uu____6159 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____6159) with
| true -> begin
(((Prims.parse_int "0")), ([]))
end
| uu____6173 -> begin
(FStar_List.fold_right (fun lb uu____6188 -> (match (uu____6188) with
| (i, out) -> begin
(

let uu____6211 = (

let uu____6214 = (

let uu____6215 = (

let uu____6221 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____6221), (i)))
in FStar_Syntax_Syntax.NM (uu____6215))
in (uu____6214)::out)
in (((i + (Prims.parse_int "1"))), (uu____6211)))
end)) lbs (((Prims.parse_int "0")), ([])))
end))
in (match (uu____6151) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____6260 = (FStar_List.fold_right (fun u uu____6280 -> (match (uu____6280) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____6260) with
| (uu____6311, u_let_rec_closing) -> begin
(

let uu___836_6319 = lb
in (

let uu____6320 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____6323 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___836_6319.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___836_6319.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____6320; FStar_Syntax_Syntax.lbeff = uu___836_6319.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____6323; FStar_Syntax_Syntax.lbattrs = uu___836_6319.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___836_6319.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_closing t)
in ((lbs1), (t1))))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____6339 -> (match (uu____6339) with
| (us, t) -> begin
(

let n1 = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____6374 -> (match (uu____6374) with
| (x, uu____6383) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n1 - i)))))
end)) binders)
in (

let t1 = (subst s t)
in ((us), (t1))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____6404 -> (match (uu____6404) with
| (us', t) -> begin
(

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n1 - i)))))) us)
in (

let uu____6428 = (subst s t)
in ((us'), (uu____6428))))))
end))


let subst_tscheme : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun s uu____6447 -> (match (uu____6447) with
| (us, t) -> begin
(

let s1 = (shift_subst (FStar_List.length us) s)
in (

let uu____6461 = (subst s1 t)
in ((us), (uu____6461))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n1 = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____6502 -> (match (uu____6502) with
| (x, uu____6511) -> begin
FStar_Syntax_Syntax.DB ((((n1 - i)), (x)))
end))))))


let closing_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (closing_subst bs))


let open_term_1 : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term) = (fun b t -> (

let uu____6538 = (open_term ((b)::[]) t)
in (match (uu____6538) with
| ((b1)::[], t1) -> begin
((b1), (t1))
end
| uu____6579 -> begin
(failwith "impossible: open_term_1")
end)))


let open_term_bvs : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun bvs t -> (

let uu____6610 = (

let uu____6615 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (open_term uu____6615 t))
in (match (uu____6610) with
| (bs, t1) -> begin
(

let uu____6630 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in ((uu____6630), (t1)))
end)))


let open_term_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun bv t -> (

let uu____6658 = (open_term_bvs ((bv)::[]) t)
in (match (uu____6658) with
| ((bv1)::[], t1) -> begin
((bv1), (t1))
end
| uu____6673 -> begin
(failwith "impossible: open_term_bv")
end)))




