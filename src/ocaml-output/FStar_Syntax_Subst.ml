
open Prims
open FStar_Pervasives

let subst_to_string : 'Auu____5 . (FStar_Syntax_Syntax.bv * 'Auu____5) Prims.list  ->  Prims.string = (fun s -> (

let uu____23 = (FStar_All.pipe_right s (FStar_List.map (fun uu____41 -> (match (uu____41) with
| (b, uu____47) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right uu____23 (FStar_String.concat ", "))))


let rec apply_until_some : 'Auu____58 'Auu____59 . ('Auu____58  ->  'Auu____59 FStar_Pervasives_Native.option)  ->  'Auu____58 Prims.list  ->  ('Auu____58 Prims.list * 'Auu____59) FStar_Pervasives_Native.option = (fun f s -> (match (s) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (s0)::rest -> begin
(

let uu____101 = (f s0)
in (match (uu____101) with
| FStar_Pervasives_Native.None -> begin
(apply_until_some f rest)
end
| FStar_Pervasives_Native.Some (st) -> begin
FStar_Pervasives_Native.Some (((rest), (st)))
end))
end))


let map_some_curry : 'Auu____133 'Auu____134 'Auu____135 . ('Auu____133  ->  'Auu____134  ->  'Auu____135)  ->  'Auu____135  ->  ('Auu____133 * 'Auu____134) FStar_Pervasives_Native.option  ->  'Auu____135 = (fun f x uu___90_162 -> (match (uu___90_162) with
| FStar_Pervasives_Native.None -> begin
x
end
| FStar_Pervasives_Native.Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map : 'Auu____197 'Auu____198 'Auu____199 . ('Auu____197  ->  'Auu____198 FStar_Pervasives_Native.option)  ->  'Auu____197 Prims.list  ->  ('Auu____197 Prims.list  ->  'Auu____198  ->  'Auu____199)  ->  'Auu____199  ->  'Auu____199 = (fun f s g t -> (

let uu____247 = (apply_until_some f s)
in (FStar_All.pipe_right uu____247 (map_some_curry g t))))


let compose_subst : 'Auu____272 . ('Auu____272 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  ('Auu____272 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  ('Auu____272 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) = (fun s1 s2 -> (

let s = (FStar_List.append (FStar_Pervasives_Native.fst s1) (FStar_Pervasives_Native.fst s2))
in (

let ropt = (match ((FStar_Pervasives_Native.snd s2)) with
| FStar_Syntax_Syntax.SomeUseRange (uu____323) -> begin
(FStar_Pervasives_Native.snd s2)
end
| uu____326 -> begin
(FStar_Pervasives_Native.snd s1)
end)
in ((s), (ropt)))))


let delay : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.term = (fun t s -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t'), ((compose_subst s' s))) t.FStar_Syntax_Syntax.pos)
end
| uu____408 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed ((t), (s)) t.FStar_Syntax_Syntax.pos)
end))


let rec force_uvar' : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar ({FStar_Syntax_Syntax.ctx_uvar_head = uv; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____431; FStar_Syntax_Syntax.ctx_uvar_binders = uu____432; FStar_Syntax_Syntax.ctx_uvar_typ = uu____433; FStar_Syntax_Syntax.ctx_uvar_reason = uu____434; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____435; FStar_Syntax_Syntax.ctx_uvar_range = uu____436}, s) -> begin
(

let uu____476 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____476) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____486 = (

let uu____489 = (

let uu____496 = (delay t' s)
in (force_uvar' uu____496))
in (FStar_Pervasives_Native.fst uu____489))
in ((uu____486), (true)))
end
| uu____503 -> begin
((t), (false))
end))
end
| uu____508 -> begin
((t), (false))
end))


let force_uvar : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (

let uu____526 = (force_uvar' t)
in (match (uu____526) with
| (t', forced) -> begin
(match ((not (forced))) with
| true -> begin
((t), (forced))
end
| uu____553 -> begin
(

let uu____554 = (delay t' (([]), (FStar_Syntax_Syntax.SomeUseRange (t.FStar_Syntax_Syntax.pos))))
in ((uu____554), (forced)))
end)
end)))


let rec try_read_memo_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(

let uu____624 = (FStar_ST.op_Bang m)
in (match (uu____624) with
| FStar_Pervasives_Native.None -> begin
((t), (false))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____693 = (try_read_memo_aux t')
in (match (uu____693) with
| (t'1, shorten) -> begin
((match (shorten) with
| true -> begin
(FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some (t'1)))
end
| uu____764 -> begin
()
end);
((t'1), (true));
)
end))
end))
end
| uu____767 -> begin
((t), (false))
end))


let try_read_memo : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____781 = (try_read_memo_aux t)
in (FStar_Pervasives_Native.fst uu____781)))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(

let uu____804 = (FStar_Syntax_Unionfind.univ_find u')
in (match (uu____804) with
| FStar_Pervasives_Native.Some (u1) -> begin
(compress_univ u1)
end
| uu____808 -> begin
u
end))
end
| uu____811 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___91_832 -> (match (uu___91_832) with
| FStar_Syntax_Syntax.DB (i, x) when (Prims.op_Equality i a.FStar_Syntax_Syntax.index) -> begin
(

let uu____837 = (

let uu____838 = (

let uu____839 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x uu____839))
in (FStar_Syntax_Syntax.bv_to_name uu____838))
in FStar_Pervasives_Native.Some (uu____837))
end
| uu____840 -> begin
FStar_Pervasives_Native.None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___92_865 -> (match (uu___92_865) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____872 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___98_877 = a
in {FStar_Syntax_Syntax.ppname = uu___98_877.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___98_877.FStar_Syntax_Syntax.sort}))
in FStar_Pervasives_Native.Some (uu____872))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____888 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___93_910 -> (match (uu___93_910) with
| FStar_Syntax_Syntax.UN (y, t) when (Prims.op_Equality x y) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____915 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___94_935 -> (match (uu___94_935) with
| FStar_Syntax_Syntax.UD (y, i) when (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____940 -> begin
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
| FStar_Syntax_Syntax.U_unif (uu____966) -> begin
u1
end
| FStar_Syntax_Syntax.U_succ (u2) -> begin
(

let uu____976 = (subst_univ s u2)
in FStar_Syntax_Syntax.U_succ (uu____976))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____980 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (uu____980))
end)))


let tag_with_range : 'Auu____989 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ('Auu____989 * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Syntax_Syntax.NoUseRange -> begin
t
end
| FStar_Syntax_Syntax.SomeUseRange (r) -> begin
(

let uu____1015 = (

let uu____1016 = (FStar_Range.use_range t.FStar_Syntax_Syntax.pos)
in (

let uu____1017 = (FStar_Range.use_range r)
in (FStar_Range.rng_included uu____1016 uu____1017)))
in (match (uu____1015) with
| true -> begin
t
end
| uu____1020 -> begin
(

let r1 = (

let uu____1022 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1022))
in (

let t' = (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____1025 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_bvar (uu____1025))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____1027 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_name (uu____1027))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v1 = (

let uu___99_1033 = fv.FStar_Syntax_Syntax.fv_name
in (

let uu____1034 = (FStar_Ident.set_lid_range l r1)
in {FStar_Syntax_Syntax.v = uu____1034; FStar_Syntax_Syntax.p = uu___99_1033.FStar_Syntax_Syntax.p}))
in (

let fv1 = (

let uu___100_1036 = fv
in {FStar_Syntax_Syntax.fv_name = v1; FStar_Syntax_Syntax.fv_delta = uu___100_1036.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___100_1036.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv1))))
end
| t' -> begin
t'
end)
in (

let uu___101_1038 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___101_1038.FStar_Syntax_Syntax.vars})))
end))
end))


let tag_lid_with_range : 'Auu____1047 . FStar_Ident.lident  ->  ('Auu____1047 * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Ident.lident = (fun l s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Syntax_Syntax.NoUseRange -> begin
l
end
| FStar_Syntax_Syntax.SomeUseRange (r) -> begin
(

let uu____1067 = (

let uu____1068 = (

let uu____1069 = (FStar_Ident.range_of_lid l)
in (FStar_Range.use_range uu____1069))
in (

let uu____1070 = (FStar_Range.use_range r)
in (FStar_Range.rng_included uu____1068 uu____1070)))
in (match (uu____1067) with
| true -> begin
l
end
| uu____1071 -> begin
(

let uu____1072 = (

let uu____1073 = (FStar_Ident.range_of_lid l)
in (

let uu____1074 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range uu____1073 uu____1074)))
in (FStar_Ident.set_lid_range l uu____1072))
end))
end))


let mk_range : FStar_Range.range  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Range.range = (fun r s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Syntax_Syntax.NoUseRange -> begin
r
end
| FStar_Syntax_Syntax.SomeUseRange (r') -> begin
(

let uu____1090 = (

let uu____1091 = (FStar_Range.use_range r)
in (

let uu____1092 = (FStar_Range.use_range r')
in (FStar_Range.rng_included uu____1091 uu____1092)))
in (match (uu____1090) with
| true -> begin
r
end
| uu____1093 -> begin
(

let uu____1094 = (FStar_Range.use_range r')
in (FStar_Range.set_use_range r uu____1094))
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
| uu____1206 -> begin
(

let t0 = (try_read_memo t)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1214) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1219) -> begin
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

let uu____1288 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (

let uu____1289 = (

let uu____1296 = (

let uu____1297 = (subst_univ (FStar_Pervasives_Native.fst s) u)
in FStar_Syntax_Syntax.Tm_type (uu____1297))
in (FStar_Syntax_Syntax.mk uu____1296))
in (uu____1289 FStar_Pervasives_Native.None uu____1288)))
end
| uu____1305 -> begin
(

let uu____1306 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed ((t0), (s)) uu____1306))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___95_1318 -> (match (uu___95_1318) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(

let uu____1322 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (uu____1322))
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
| uu____1350 -> begin
(

let uu___102_1359 = t
in (

let uu____1360 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____1365 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____1370 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____1373 = (FStar_List.map (fun uu____1400 -> (match (uu____1400) with
| (t1, imp) -> begin
(

let uu____1419 = (subst' s t1)
in ((uu____1419), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (

let uu____1422 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu____1360; FStar_Syntax_Syntax.effect_name = uu____1365; FStar_Syntax_Syntax.result_typ = uu____1370; FStar_Syntax_Syntax.effect_args = uu____1373; FStar_Syntax_Syntax.flags = uu____1422}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| (([])::[], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| uu____1453 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uopt) -> begin
(

let uu____1474 = (subst' s t1)
in (

let uu____1475 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____1474 uu____1475)))
end
| FStar_Syntax_Syntax.GTotal (t1, uopt) -> begin
(

let uu____1492 = (subst' s t1)
in (

let uu____1493 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1492 uu____1493)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1501 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp uu____1501))
end)
end))
and subst_imp' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun s i -> (match (i) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____1511 = (

let uu____1512 = (subst' s t)
in FStar_Syntax_Syntax.Meta (uu____1512))
in FStar_Pervasives_Native.Some (uu____1511))
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
| FStar_Syntax_Syntax.NT (uu____1536) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n1 s -> (FStar_List.map (shift n1) s))


let shift_subst' : 'Auu____1559 . Prims.int  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1559)  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1559) = (fun n1 s -> (

let uu____1588 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (shift_subst n1)))
in ((uu____1588), ((FStar_Pervasives_Native.snd s)))))


let subst_binder' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun s uu____1622 -> (match (uu____1622) with
| (x, imp) -> begin
(

let uu____1641 = (

let uu___103_1642 = x
in (

let uu____1643 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___103_1642.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___103_1642.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1643}))
in (

let uu____1646 = (subst_imp' s imp)
in ((uu____1641), (uu____1646))))
end))


let subst_binders' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1745 -> begin
(

let uu____1746 = (shift_subst' i s)
in (subst_binder' uu____1746 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) bs))


let subst_arg' : 'Auu____1775 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term * 'Auu____1775)  ->  (FStar_Syntax_Syntax.term * 'Auu____1775) = (fun s uu____1793 -> (match (uu____1793) with
| (t, imp) -> begin
(

let uu____1800 = (subst' s t)
in ((uu____1800), (imp)))
end))


let subst_args' : 'Auu____1806 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term * 'Auu____1806) Prims.list  ->  (FStar_Syntax_Syntax.term * 'Auu____1806) Prims.list = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____1893) -> begin
((p1), (n1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1912 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1966 uu____1967 -> (match (((uu____1966), (uu____1967))) with
| ((pats1, n2), (p2, imp)) -> begin
(

let uu____2046 = (aux n2 p2)
in (match (uu____2046) with
| (p3, m) -> begin
(((((p3), (imp)))::pats1), (m))
end))
end)) (([]), (n1))))
in (match (uu____1912) with
| (pats1, n2) -> begin
(((

let uu___104_2102 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___104_2102.FStar_Syntax_Syntax.p})), (n2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___105_2126 = x
in (

let uu____2127 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___105_2126.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___105_2126.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2127}))
in (((

let uu___106_2131 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___106_2131.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___107_2143 = x
in (

let uu____2144 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___107_2143.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___107_2143.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2144}))
in (((

let uu___108_2148 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___108_2148.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___109_2165 = x
in (

let uu____2166 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___109_2165.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___109_2165.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2166}))
in (

let t01 = (subst' s1 t0)
in (((

let uu___110_2171 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___110_2171.FStar_Syntax_Syntax.p})), (n1)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s lopt -> (match (lopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____2195 = (

let uu___111_2196 = rc
in (

let uu____2197 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (subst' s))
in {FStar_Syntax_Syntax.residual_effect = uu___111_2196.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____2197; FStar_Syntax_Syntax.residual_flags = uu___111_2196.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____2195))
end))


let compose_uvar_subst : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts = (fun u s0 s -> (

let should_retain = (fun x -> (FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders (FStar_Util.for_some (fun uu____2244 -> (match (uu____2244) with
| (x', uu____2252) -> begin
(FStar_Syntax_Syntax.bv_eq x x')
end)))))
in (

let rec aux = (fun uu___97_2268 -> (match (uu___97_2268) with
| [] -> begin
[]
end
| (hd_subst)::rest -> begin
(

let hd1 = (FStar_All.pipe_right hd_subst (FStar_List.collect (fun uu___96_2299 -> (match (uu___96_2299) with
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____2308 = (should_retain x)
in (match (uu____2308) with
| true -> begin
(

let uu____2311 = (

let uu____2312 = (

let uu____2319 = (delay t ((rest), (FStar_Syntax_Syntax.NoUseRange)))
in ((x), (uu____2319)))
in FStar_Syntax_Syntax.NT (uu____2312))
in (uu____2311)::[])
end
| uu____2328 -> begin
[]
end))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____2331 = (should_retain x)
in (match (uu____2331) with
| true -> begin
(

let x_i = (FStar_Syntax_Syntax.bv_to_tm (

let uu___112_2337 = x
in {FStar_Syntax_Syntax.ppname = uu___112_2337.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___112_2337.FStar_Syntax_Syntax.sort}))
in (

let t = (subst' ((rest), (FStar_Syntax_Syntax.NoUseRange)) x_i)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x_j) -> begin
(FStar_Syntax_Syntax.NM (((x), (x_j.FStar_Syntax_Syntax.index))))::[]
end
| uu____2346 -> begin
(FStar_Syntax_Syntax.NT (((x), (t))))::[]
end)))
end
| uu____2349 -> begin
[]
end))
end
| uu____2350 -> begin
[]
end))))
in (

let uu____2351 = (aux rest)
in (FStar_List.append hd1 uu____2351)))
end))
in (

let uu____2354 = (aux (FStar_List.append (FStar_Pervasives_Native.fst s0) (FStar_Pervasives_Native.fst s)))
in (match (uu____2354) with
| [] -> begin
(([]), ((FStar_Pervasives_Native.snd s)))
end
| s' -> begin
(((s')::[]), ((FStar_Pervasives_Native.snd s)))
end)))))


let rec push_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk1 = (fun t' -> (

let uu____2416 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2416)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2419) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
t
end
| FStar_Syntax_Syntax.Tm_constant (uu____2445) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2450) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_uvar (uv, s0) -> begin
(

let uu____2477 = (FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____2477) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2482 = (

let uu___113_2485 = t
in (

let uu____2488 = (

let uu____2489 = (

let uu____2502 = (compose_uvar_subst uv s0 s)
in ((uv), (uu____2502)))
in FStar_Syntax_Syntax.Tm_uvar (uu____2489))
in {FStar_Syntax_Syntax.n = uu____2488; FStar_Syntax_Syntax.pos = uu___113_2485.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___113_2485.FStar_Syntax_Syntax.vars}))
in (tag_with_range uu____2482 s))
end
| FStar_Pervasives_Native.Some (t1) -> begin
(push_subst (compose_subst s0 s) t1)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____2526) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2527) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_name (uu____2528) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us1 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us)
in (

let uu____2542 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us1)
in (tag_with_range uu____2542 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(

let uu____2575 = (

let uu____2576 = (

let uu____2593 = (subst' s t0)
in (

let uu____2596 = (subst_args' s args)
in ((uu____2593), (uu____2596))))
in FStar_Syntax_Syntax.Tm_app (uu____2576))
in (mk1 uu____2575))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t1) -> begin
(

let uu____2697 = (subst' s t1)
in FStar_Util.Inl (uu____2697))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2711 = (subst_comp' s c)
in FStar_Util.Inr (uu____2711))
end)
in (

let uu____2718 = (

let uu____2719 = (

let uu____2746 = (subst' s t0)
in (

let uu____2749 = (

let uu____2766 = (FStar_Util.map_opt topt (subst' s))
in ((annot1), (uu____2766)))
in ((uu____2746), (uu____2749), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2719))
in (mk1 uu____2718)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n1 = (FStar_List.length bs)
in (

let s' = (shift_subst' n1 s)
in (

let uu____2852 = (

let uu____2853 = (

let uu____2872 = (subst_binders' s bs)
in (

let uu____2881 = (subst' s' body)
in (

let uu____2884 = (push_subst_lcomp s' lopt)
in ((uu____2872), (uu____2881), (uu____2884)))))
in FStar_Syntax_Syntax.Tm_abs (uu____2853))
in (mk1 uu____2852))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n1 = (FStar_List.length bs)
in (

let uu____2928 = (

let uu____2929 = (

let uu____2944 = (subst_binders' s bs)
in (

let uu____2953 = (

let uu____2956 = (shift_subst' n1 s)
in (subst_comp' uu____2956 comp))
in ((uu____2944), (uu____2953))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2929))
in (mk1 uu____2928)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x1 = (

let uu___114_2986 = x
in (

let uu____2987 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___114_2986.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___114_2986.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2987}))
in (

let phi1 = (

let uu____2991 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____2991 phi))
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((x1), (phi1)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t01 = (subst' s t0)
in (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____3106 -> (match (uu____3106) with
| (pat, wopt, branch) -> begin
(

let uu____3136 = (subst_pat' s pat)
in (match (uu____3136) with
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

let uu____3164 = (subst' s1 w)
in FStar_Pervasives_Native.Some (uu____3164))
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

let uu____3233 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____3233) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____3236 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___115_3248 = x
in {FStar_Syntax_Syntax.ppname = uu___115_3248.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_3248.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr (fv)
end)
in (

let uu___116_3250 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___116_3250.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___116_3250.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd; FStar_Syntax_Syntax.lbattrs = uu___116_3250.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___116_3250.FStar_Syntax_Syntax.lbpos})))))))
in (mk1 (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs1))), (body1)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let uu____3279 = (

let uu____3280 = (

let uu____3287 = (subst' s t0)
in (

let uu____3290 = (

let uu____3291 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____3291))
in ((uu____3287), (uu____3290))))
in FStar_Syntax_Syntax.Tm_meta (uu____3280))
in (mk1 uu____3279))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) -> begin
(

let uu____3357 = (

let uu____3358 = (

let uu____3365 = (subst' s t0)
in (

let uu____3368 = (

let uu____3369 = (

let uu____3376 = (subst' s t1)
in ((m), (uu____3376)))
in FStar_Syntax_Syntax.Meta_monadic (uu____3369))
in ((uu____3365), (uu____3368))))
in FStar_Syntax_Syntax.Tm_meta (uu____3358))
in (mk1 uu____3357))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) -> begin
(

let uu____3395 = (

let uu____3396 = (

let uu____3403 = (subst' s t0)
in (

let uu____3406 = (

let uu____3407 = (

let uu____3416 = (subst' s t1)
in ((m1), (m2), (uu____3416)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____3407))
in ((uu____3403), (uu____3406))))
in FStar_Syntax_Syntax.Tm_meta (uu____3396))
in (mk1 uu____3395))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____3431 = (

let uu____3432 = (

let uu____3439 = (subst' s tm)
in ((uu____3439), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____3432))
in (mk1 uu____3431))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted (subst' s) qi)
in (mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi1))))))
end)
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____3453 = (

let uu____3454 = (

let uu____3461 = (subst' s t1)
in ((uu____3461), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____3454))
in (mk1 uu____3453))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (try_read_memo t)
in (

let uu____3474 = (force_uvar t1)
in (match (uu____3474) with
| (t2, uu____3482) -> begin
(match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s), memo) -> begin
((

let uu____3533 = (

let uu____3538 = (push_subst s t')
in FStar_Pervasives_Native.Some (uu____3538))
in (FStar_ST.op_Colon_Equals memo uu____3533));
(compress t2);
)
end
| uu____3592 -> begin
t2
end)
end))))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (

let uu____3625 = (

let uu____3626 = (

let uu____3627 = (

let uu____3628 = (FStar_Range.use_range r)
in (FStar_Range.set_def_range r uu____3628))
in FStar_Syntax_Syntax.SomeUseRange (uu____3627))
in (([]), (uu____3626)))
in (subst' uu____3625 t)))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) t))


let subst_imp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun s imp -> (subst_imp' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) imp))


let closing_subst : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun bs -> (

let uu____3692 = (FStar_List.fold_right (fun uu____3717 uu____3718 -> (match (((uu____3717), (uu____3718))) with
| ((x, uu____3750), (subst1, n1)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n1))))::subst1), ((n1 + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____3692 FStar_Pervasives_Native.fst)))


let open_binders' : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun bs -> (

let rec aux = (fun bs1 o -> (match (bs1) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___117_3925 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____3926 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___117_3925.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___117_3925.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3926}))
in (

let imp1 = (subst_imp o imp)
in (

let o1 = (

let uu____3935 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____3935)
in (

let uu____3938 = (aux bs' o1)
in (match (uu____3938) with
| (bs'1, o2) -> begin
(((((x'), (imp1)))::bs'1), (o2))
end)))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____4012 = (open_binders' bs)
in (FStar_Pervasives_Native.fst uu____4012)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____4053 = (open_binders' bs)
in (match (uu____4053) with
| (bs', opening) -> begin
(

let uu____4096 = (subst opening t)
in ((bs'), (uu____4096), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____4111 = (open_term' bs t)
in (match (uu____4111) with
| (b, t1, uu____4124) -> begin
((b), (t1))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____4139 = (open_binders' bs)
in (match (uu____4139) with
| (bs', opening) -> begin
(

let uu____4180 = (subst_comp opening t)
in ((bs'), (uu____4180)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec open_pat_aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4229) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4252 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4318 uu____4319 -> (match (((uu____4318), (uu____4319))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____4422 = (open_pat_aux sub2 p2)
in (match (uu____4422) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4252) with
| (pats1, sub2) -> begin
(((

let uu___118_4524 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___118_4524.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___119_4543 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4544 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___119_4543.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___119_4543.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4544}))
in (

let sub2 = (

let uu____4550 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4550)
in (((

let uu___120_4558 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.p = uu___120_4558.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___121_4563 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4564 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___121_4563.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___121_4563.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4564}))
in (

let sub2 = (

let uu____4570 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4570)
in (((

let uu___122_4578 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.p = uu___122_4578.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___123_4588 = x
in (

let uu____4589 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___123_4588.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_4588.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4589}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___124_4598 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___124_4598.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (open_pat_aux [] p)))


let open_branch' : FStar_Syntax_Syntax.branch  ->  (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t) = (fun uu____4611 -> (match (uu____4611) with
| (p, wopt, e) -> begin
(

let uu____4635 = (open_pat p)
in (match (uu____4635) with
| (p1, opening) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____4664 = (subst opening w)
in FStar_Pervasives_Native.Some (uu____4664))
end)
in (

let e1 = (subst opening e)
in ((((p1), (wopt1), (e1))), (opening))))
end))
end))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun br -> (

let uu____4683 = (open_branch' br)
in (match (uu____4683) with
| (br1, uu____4689) -> begin
br1
end)))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____4700 = (closing_subst bs)
in (subst uu____4700 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____4713 = (closing_subst bs)
in (subst_comp uu____4713 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs1 -> (match (bs1) with
| [] -> begin
[]
end
| ((x, imp))::tl1 -> begin
(

let x1 = (

let uu___125_4786 = x
in (

let uu____4787 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___125_4786.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___125_4786.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4787}))
in (

let imp1 = (subst_imp s imp)
in (

let s' = (

let uu____4796 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____4796)
in (

let uu____4799 = (aux s' tl1)
in (((x1), (imp1)))::uu____4799))))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____4831 -> (

let uu____4832 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (subst_comp s uu____4832))))))


let close_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4885) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4908 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4974 uu____4975 -> (match (((uu____4974), (uu____4975))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____5078 = (aux sub2 p2)
in (match (uu____5078) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4908) with
| (pats1, sub2) -> begin
(((

let uu___126_5180 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___126_5180.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___127_5199 = x
in (

let uu____5200 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___127_5199.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___127_5199.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5200}))
in (

let sub2 = (

let uu____5206 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5206)
in (((

let uu___128_5214 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___128_5214.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___129_5219 = x
in (

let uu____5220 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___129_5219.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___129_5219.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5220}))
in (

let sub2 = (

let uu____5226 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5226)
in (((

let uu___130_5234 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___130_5234.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___131_5244 = x
in (

let uu____5245 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___131_5244.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_5244.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5245}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___132_5254 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___132_5254.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____5263 -> (match (uu____5263) with
| (p, wopt, e) -> begin
(

let uu____5283 = (close_pat p)
in (match (uu____5283) with
| (p1, closing) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____5320 = (subst closing w)
in FStar_Pervasives_Native.Some (uu____5320))
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

let uu____5397 = (univ_var_opening us)
in (match (uu____5397) with
| (s, us') -> begin
(

let t1 = (subst s t)
in ((us'), (t1)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____5439 = (univ_var_opening us)
in (match (uu____5439) with
| (s, us') -> begin
(

let uu____5462 = (subst_comp s c)
in ((us'), (uu____5462)))
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

let uu____5518 = (

let uu____5529 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5529) with
| true -> begin
(((Prims.parse_int "0")), (lbs), ([]))
end
| uu____5544 -> begin
(FStar_List.fold_right (fun lb uu____5562 -> (match (uu____5562) with
| (i, lbs1, out) -> begin
(

let x = (

let uu____5595 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____5595))
in (((i + (Prims.parse_int "1"))), (((

let uu___133_5601 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___133_5601.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___133_5601.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___133_5601.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___133_5601.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___133_5601.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___133_5601.FStar_Syntax_Syntax.lbpos}))::lbs1), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
end))
in (match (uu____5518) with
| (n_let_recs, lbs1, let_rec_opening) -> begin
(

let lbs2 = (FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let uu____5639 = (FStar_List.fold_right (fun u uu____5667 -> (match (uu____5667) with
| (i, us, out) -> begin
(

let u1 = (FStar_Syntax_Syntax.new_univ_name FStar_Pervasives_Native.None)
in (((i + (Prims.parse_int "1"))), ((u1)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u1)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____5639) with
| (uu____5708, us, u_let_rec_opening) -> begin
(

let uu___134_5719 = lb
in (

let uu____5720 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____5723 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___134_5719.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu____5720; FStar_Syntax_Syntax.lbeff = uu___134_5719.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5723; FStar_Syntax_Syntax.lbattrs = uu___134_5719.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___134_5719.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_opening t)
in ((lbs2), (t1))))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____5749 = (

let uu____5756 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5756) with
| true -> begin
(((Prims.parse_int "0")), ([]))
end
| uu____5765 -> begin
(FStar_List.fold_right (fun lb uu____5778 -> (match (uu____5778) with
| (i, out) -> begin
(

let uu____5797 = (

let uu____5800 = (

let uu____5801 = (

let uu____5806 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____5806), (i)))
in FStar_Syntax_Syntax.NM (uu____5801))
in (uu____5800)::out)
in (((i + (Prims.parse_int "1"))), (uu____5797)))
end)) lbs (((Prims.parse_int "0")), ([])))
end))
in (match (uu____5749) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____5838 = (FStar_List.fold_right (fun u uu____5856 -> (match (uu____5856) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____5838) with
| (uu____5879, u_let_rec_closing) -> begin
(

let uu___135_5885 = lb
in (

let uu____5886 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____5889 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___135_5885.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___135_5885.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____5886; FStar_Syntax_Syntax.lbeff = uu___135_5885.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5889; FStar_Syntax_Syntax.lbattrs = uu___135_5885.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___135_5885.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_closing t)
in ((lbs1), (t1))))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____5904 -> (match (uu____5904) with
| (us, t) -> begin
(

let n1 = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____5937 -> (match (uu____5937) with
| (x, uu____5945) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n1 - i)))))
end)) binders)
in (

let t1 = (subst s t)
in ((us), (t1))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____5970 -> (match (uu____5970) with
| (us', t) -> begin
(

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n1 - i)))))) us)
in (

let uu____5996 = (subst s t)
in ((us'), (uu____5996))))))
end))


let subst_tscheme : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun s uu____6014 -> (match (uu____6014) with
| (us, t) -> begin
(

let s1 = (shift_subst (FStar_List.length us) s)
in (

let uu____6028 = (subst s1 t)
in ((us), (uu____6028))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n1 = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____6066 -> (match (uu____6066) with
| (x, uu____6074) -> begin
FStar_Syntax_Syntax.DB ((((n1 - i)), (x)))
end))))))


let closing_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (closing_subst bs))


let open_term_1 : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term) = (fun b t -> (

let uu____6098 = (open_term ((b)::[]) t)
in (match (uu____6098) with
| ((b1)::[], t1) -> begin
((b1), (t1))
end
| uu____6139 -> begin
(failwith "impossible: open_term_1")
end)))


let open_term_bvs : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun bvs t -> (

let uu____6168 = (

let uu____6173 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (open_term uu____6173 t))
in (match (uu____6168) with
| (bs, t1) -> begin
(

let uu____6188 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in ((uu____6188), (t1)))
end)))


let open_term_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun bv t -> (

let uu____6215 = (open_term_bvs ((bv)::[]) t)
in (match (uu____6215) with
| ((bv1)::[], t1) -> begin
((bv1), (t1))
end
| uu____6230 -> begin
(failwith "impossible: open_term_bv")
end)))




