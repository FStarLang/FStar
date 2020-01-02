
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


let force_uvar : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____557 = (force_uvar' t)
in (match (uu____557) with
| (t', forced) -> begin
(match (forced) with
| true -> begin
(delay t' (([]), (FStar_Syntax_Syntax.SomeUseRange (t.FStar_Syntax_Syntax.pos))))
end
| uu____584 -> begin
t
end)
end)))


let rec try_read_memo_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(

let uu____648 = (FStar_ST.op_Bang m)
in (match (uu____648) with
| FStar_Pervasives_Native.None -> begin
((t), (false))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____698 = (try_read_memo_aux t')
in (match (uu____698) with
| (t'1, shorten) -> begin
((match (shorten) with
| true -> begin
(FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some (t'1)))
end
| uu____752 -> begin
()
end);
((t'1), (true));
)
end))
end))
end
| uu____758 -> begin
((t), (false))
end))


let try_read_memo : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____775 = (try_read_memo_aux t)
in (FStar_Pervasives_Native.fst uu____775)))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(

let uu____801 = (FStar_Syntax_Unionfind.univ_find u')
in (match (uu____801) with
| FStar_Pervasives_Native.Some (u1) -> begin
(compress_univ u1)
end
| uu____805 -> begin
u
end))
end
| uu____808 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___1_830 -> (match (uu___1_830) with
| FStar_Syntax_Syntax.DB (i, x) when (Prims.op_Equality i a.FStar_Syntax_Syntax.index) -> begin
(

let uu____838 = (

let uu____839 = (

let uu____840 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x uu____840))
in (FStar_Syntax_Syntax.bv_to_name uu____839))
in FStar_Pervasives_Native.Some (uu____838))
end
| uu____841 -> begin
FStar_Pervasives_Native.None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun a s -> (FStar_Util.find_map s (fun uu___2_867 -> (match (uu___2_867) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____876 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___108_881 = a
in {FStar_Syntax_Syntax.ppname = uu___108_881.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___108_881.FStar_Syntax_Syntax.sort}))
in FStar_Pervasives_Native.Some (uu____876))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____892 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___3_917 -> (match (uu___3_917) with
| FStar_Syntax_Syntax.UN (y, t) when (Prims.op_Equality x y) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____925 -> begin
FStar_Pervasives_Native.None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun x s -> (FStar_Util.find_map s (fun uu___4_946 -> (match (uu___4_946) with
| FStar_Syntax_Syntax.UD (y, i) when (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____954 -> begin
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
| FStar_Syntax_Syntax.U_unif (uu____982) -> begin
u1
end
| FStar_Syntax_Syntax.U_succ (u2) -> begin
(

let uu____992 = (subst_univ s u2)
in FStar_Syntax_Syntax.U_succ (uu____992))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____996 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (uu____996))
end)))


let tag_with_range : 'Auu____1006 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ('Auu____1006 * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Syntax_Syntax.NoUseRange -> begin
t
end
| FStar_Syntax_Syntax.SomeUseRange (r) -> begin
(

let uu____1032 = (

let uu____1034 = (FStar_Range.use_range t.FStar_Syntax_Syntax.pos)
in (

let uu____1035 = (FStar_Range.use_range r)
in (FStar_Range.rng_included uu____1034 uu____1035)))
in (match (uu____1032) with
| true -> begin
t
end
| uu____1039 -> begin
(

let r1 = (

let uu____1042 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1042))
in (

let t' = (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____1045 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_bvar (uu____1045))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____1047 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_name (uu____1047))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v1 = (

let uu___160_1053 = fv.FStar_Syntax_Syntax.fv_name
in (

let uu____1054 = (FStar_Ident.set_lid_range l r1)
in {FStar_Syntax_Syntax.v = uu____1054; FStar_Syntax_Syntax.p = uu___160_1053.FStar_Syntax_Syntax.p}))
in (

let fv1 = (

let uu___163_1056 = fv
in {FStar_Syntax_Syntax.fv_name = v1; FStar_Syntax_Syntax.fv_delta = uu___163_1056.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___163_1056.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv1))))
end
| t' -> begin
t'
end)
in (

let uu___168_1058 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___168_1058.FStar_Syntax_Syntax.vars})))
end))
end))


let tag_lid_with_range : 'Auu____1068 . FStar_Ident.lident  ->  ('Auu____1068 * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Ident.lident = (fun l s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Syntax_Syntax.NoUseRange -> begin
l
end
| FStar_Syntax_Syntax.SomeUseRange (r) -> begin
(

let uu____1088 = (

let uu____1090 = (

let uu____1091 = (FStar_Ident.range_of_lid l)
in (FStar_Range.use_range uu____1091))
in (

let uu____1092 = (FStar_Range.use_range r)
in (FStar_Range.rng_included uu____1090 uu____1092)))
in (match (uu____1088) with
| true -> begin
l
end
| uu____1094 -> begin
(

let uu____1096 = (

let uu____1097 = (FStar_Ident.range_of_lid l)
in (

let uu____1098 = (FStar_Range.use_range r)
in (FStar_Range.set_use_range uu____1097 uu____1098)))
in (FStar_Ident.set_lid_range l uu____1096))
end))
end))


let mk_range : FStar_Range.range  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Range.range = (fun r s -> (match ((FStar_Pervasives_Native.snd s)) with
| FStar_Syntax_Syntax.NoUseRange -> begin
r
end
| FStar_Syntax_Syntax.SomeUseRange (r') -> begin
(

let uu____1115 = (

let uu____1117 = (FStar_Range.use_range r)
in (

let uu____1118 = (FStar_Range.use_range r')
in (FStar_Range.rng_included uu____1117 uu____1118)))
in (match (uu____1115) with
| true -> begin
r
end
| uu____1120 -> begin
(

let uu____1122 = (FStar_Range.use_range r')
in (FStar_Range.set_use_range r uu____1122))
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
| uu____1175 -> begin
(

let t0 = (try_read_memo t)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1183) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1188) -> begin
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

let uu____1257 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (

let uu____1258 = (

let uu____1265 = (

let uu____1266 = (subst_univ (FStar_Pervasives_Native.fst s) u)
in FStar_Syntax_Syntax.Tm_type (uu____1266))
in (FStar_Syntax_Syntax.mk uu____1265))
in (uu____1258 FStar_Pervasives_Native.None uu____1257)))
end
| uu____1271 -> begin
(

let uu____1272 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed ((t0), (s)) uu____1272))
end))
end)))


let subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___5_1297 -> (match (uu___5_1297) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(

let uu____1301 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (uu____1301))
end
| f -> begin
f
end)))))


let subst_imp' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun s i -> (match (i) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____1327 = (

let uu____1328 = (subst' s t)
in FStar_Syntax_Syntax.Meta (uu____1328))
in FStar_Pervasives_Native.Some (uu____1327))
end
| i1 -> begin
i1
end))


let subst_comp_typ' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| ([], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| (([])::[], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| uu____1375 -> begin
(

let uu___235_1384 = t
in (

let uu____1385 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____1390 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____1395 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____1398 = (FStar_List.map (fun uu____1426 -> (match (uu____1426) with
| (t1, imp) -> begin
(

let uu____1445 = (subst' s t1)
in (

let uu____1446 = (subst_imp' s imp)
in ((uu____1445), (uu____1446))))
end)) t.FStar_Syntax_Syntax.effect_args)
in (

let uu____1451 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu____1385; FStar_Syntax_Syntax.effect_name = uu____1390; FStar_Syntax_Syntax.result_typ = uu____1395; FStar_Syntax_Syntax.effect_args = uu____1398; FStar_Syntax_Syntax.flags = uu____1451}))))))
end))


let subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| (([])::[], FStar_Syntax_Syntax.NoUseRange) -> begin
t
end
| uu____1503 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uopt) -> begin
(

let uu____1524 = (subst' s t1)
in (

let uu____1525 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____1524 uu____1525)))
end
| FStar_Syntax_Syntax.GTotal (t1, uopt) -> begin
(

let uu____1542 = (subst' s t1)
in (

let uu____1543 = (FStar_Option.map (subst_univ (FStar_Pervasives_Native.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1542 uu____1543)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1551 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp uu____1551))
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
| FStar_Syntax_Syntax.NT (uu____1585) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n1 s -> (FStar_List.map (shift n1) s))


let shift_subst' : 'Auu____1612 . Prims.int  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1612)  ->  (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1612) = (fun n1 s -> (

let uu____1643 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst s) (FStar_List.map (shift_subst n1)))
in ((uu____1643), ((FStar_Pervasives_Native.snd s)))))


let subst_binder' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun s uu____1678 -> (match (uu____1678) with
| (x, imp) -> begin
(

let uu____1697 = (

let uu___288_1698 = x
in (

let uu____1699 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___288_1698.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___288_1698.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1699}))
in (

let uu____1702 = (subst_imp' s imp)
in ((uu____1697), (uu____1702))))
end))


let subst_binders' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1806 -> begin
(

let uu____1808 = (shift_subst' i s)
in (subst_binder' uu____1808 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) bs))


let subst_arg' : 'Auu____1839 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term * 'Auu____1839)  ->  (FStar_Syntax_Syntax.term * 'Auu____1839) = (fun s uu____1857 -> (match (uu____1857) with
| (t, imp) -> begin
(

let uu____1864 = (subst' s t)
in ((uu____1864), (imp)))
end))


let subst_args' : 'Auu____1871 . FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term * 'Auu____1871) Prims.list  ->  (FStar_Syntax_Syntax.term * 'Auu____1871) Prims.list = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)  ->  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____1965) -> begin
((p1), (n1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1987 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____2049 uu____2050 -> (match (((uu____2049), (uu____2050))) with
| ((pats1, n2), (p2, imp)) -> begin
(

let uu____2146 = (aux n2 p2)
in (match (uu____2146) with
| (p3, m) -> begin
(((((p3), (imp)))::pats1), (m))
end))
end)) (([]), (n1))))
in (match (uu____1987) with
| (pats1, n2) -> begin
(((

let uu___325_2220 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___325_2220.FStar_Syntax_Syntax.p})), (n2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___330_2246 = x
in (

let uu____2247 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___330_2246.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___330_2246.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2247}))
in (((

let uu___333_2252 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___333_2252.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___338_2265 = x
in (

let uu____2266 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___338_2265.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___338_2265.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2266}))
in (((

let uu___341_2271 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___341_2271.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___348_2289 = x
in (

let uu____2290 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___348_2289.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___348_2289.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2290}))
in (

let t01 = (subst' s1 t0)
in (((

let uu___352_2296 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___352_2296.FStar_Syntax_Syntax.p})), (n1)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s lopt -> (match (lopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____2322 = (

let uu___359_2323 = rc
in (

let uu____2324 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (subst' s))
in {FStar_Syntax_Syntax.residual_effect = uu___359_2323.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____2324; FStar_Syntax_Syntax.residual_flags = uu___359_2323.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____2322))
end))


let compose_uvar_subst : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts = (fun u s0 s -> (

let should_retain = (fun x -> (FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders (FStar_Util.for_some (fun uu____2374 -> (match (uu____2374) with
| (x', uu____2383) -> begin
(FStar_Syntax_Syntax.bv_eq x x')
end)))))
in (

let rec aux = (fun uu___7_2399 -> (match (uu___7_2399) with
| [] -> begin
[]
end
| (hd_subst)::rest -> begin
(

let hd1 = (FStar_All.pipe_right hd_subst (FStar_List.collect (fun uu___6_2430 -> (match (uu___6_2430) with
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____2439 = (should_retain x)
in (match (uu____2439) with
| true -> begin
(

let uu____2444 = (

let uu____2445 = (

let uu____2452 = (delay t ((rest), (FStar_Syntax_Syntax.NoUseRange)))
in ((x), (uu____2452)))
in FStar_Syntax_Syntax.NT (uu____2445))
in (uu____2444)::[])
end
| uu____2461 -> begin
[]
end))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____2467 = (should_retain x)
in (match (uu____2467) with
| true -> begin
(

let x_i = (FStar_Syntax_Syntax.bv_to_tm (

let uu___386_2475 = x
in {FStar_Syntax_Syntax.ppname = uu___386_2475.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___386_2475.FStar_Syntax_Syntax.sort}))
in (

let t = (subst' ((rest), (FStar_Syntax_Syntax.NoUseRange)) x_i)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x_j) -> begin
(FStar_Syntax_Syntax.NM (((x), (x_j.FStar_Syntax_Syntax.index))))::[]
end
| uu____2485 -> begin
(FStar_Syntax_Syntax.NT (((x), (t))))::[]
end)))
end
| uu____2488 -> begin
[]
end))
end
| uu____2490 -> begin
[]
end))))
in (

let uu____2491 = (aux rest)
in (FStar_List.append hd1 uu____2491)))
end))
in (

let uu____2494 = (aux (FStar_List.append (FStar_Pervasives_Native.fst s0) (FStar_Pervasives_Native.fst s)))
in (match (uu____2494) with
| [] -> begin
(([]), ((FStar_Pervasives_Native.snd s)))
end
| s' -> begin
(((s')::[]), ((FStar_Pervasives_Native.snd s)))
end)))))


let rec push_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk1 = (fun t' -> (

let uu____2557 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2557)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2560) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(match (i.FStar_Syntax_Syntax.lkind) with
| FStar_Syntax_Syntax.Lazy_embedding (uu____2589) -> begin
(

let t1 = (

let uu____2599 = (

let uu____2608 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____2608))
in (uu____2599 i.FStar_Syntax_Syntax.lkind i))
in (push_subst s t1))
end
| uu____2658 -> begin
t
end)
end
| FStar_Syntax_Syntax.Tm_constant (uu____2659) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2664) -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tag_with_range t s)
end
| FStar_Syntax_Syntax.Tm_uvar (uv, s0) -> begin
(

let uu____2691 = (FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____2691) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2696 = (

let uu___419_2699 = t
in (

let uu____2702 = (

let uu____2703 = (

let uu____2716 = (compose_uvar_subst uv s0 s)
in ((uv), (uu____2716)))
in FStar_Syntax_Syntax.Tm_uvar (uu____2703))
in {FStar_Syntax_Syntax.n = uu____2702; FStar_Syntax_Syntax.pos = uu___419_2699.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___419_2699.FStar_Syntax_Syntax.vars}))
in (tag_with_range uu____2696 s))
end
| FStar_Pervasives_Native.Some (t1) -> begin
(push_subst (compose_subst s0 s) t1)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____2740) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2741) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_name (uu____2742) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us1 = (FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us)
in (

let uu____2756 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us1)
in (tag_with_range uu____2756 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(

let uu____2789 = (

let uu____2790 = (

let uu____2807 = (subst' s t0)
in (

let uu____2810 = (subst_args' s args)
in ((uu____2807), (uu____2810))))
in FStar_Syntax_Syntax.Tm_app (uu____2790))
in (mk1 uu____2789))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t1) -> begin
(

let uu____2911 = (subst' s t1)
in FStar_Util.Inl (uu____2911))
end
| FStar_Util.Inr (c) -> begin
(

let uu____2925 = (subst_comp' s c)
in FStar_Util.Inr (uu____2925))
end)
in (

let uu____2932 = (

let uu____2933 = (

let uu____2960 = (subst' s t0)
in (

let uu____2963 = (

let uu____2980 = (FStar_Util.map_opt topt (subst' s))
in ((annot1), (uu____2980)))
in ((uu____2960), (uu____2963), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2933))
in (mk1 uu____2932)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n1 = (FStar_List.length bs)
in (

let s' = (shift_subst' n1 s)
in (

let uu____3062 = (

let uu____3063 = (

let uu____3082 = (subst_binders' s bs)
in (

let uu____3091 = (subst' s' body)
in (

let uu____3094 = (push_subst_lcomp s' lopt)
in ((uu____3082), (uu____3091), (uu____3094)))))
in FStar_Syntax_Syntax.Tm_abs (uu____3063))
in (mk1 uu____3062))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n1 = (FStar_List.length bs)
in (

let uu____3138 = (

let uu____3139 = (

let uu____3154 = (subst_binders' s bs)
in (

let uu____3163 = (

let uu____3166 = (shift_subst' n1 s)
in (subst_comp' uu____3166 comp))
in ((uu____3154), (uu____3163))))
in FStar_Syntax_Syntax.Tm_arrow (uu____3139))
in (mk1 uu____3138)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x1 = (

let uu___466_3192 = x
in (

let uu____3193 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___466_3192.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___466_3192.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3193}))
in (

let phi1 = (

let uu____3197 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____3197 phi))
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((x1), (phi1)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t01 = (subst' s t0)
in (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____3313 -> (match (uu____3313) with
| (pat, wopt, branch) -> begin
(

let uu____3343 = (subst_pat' s pat)
in (match (uu____3343) with
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

let uu____3374 = (subst' s1 w)
in FStar_Pervasives_Native.Some (uu____3374))
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

let uu____3442 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____3442) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____3447 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___504_3460 = x
in {FStar_Syntax_Syntax.ppname = uu___504_3460.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___504_3460.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr (fv)
end)
in (

let uu___509_3462 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___509_3462.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___509_3462.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd; FStar_Syntax_Syntax.lbattrs = uu___509_3462.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___509_3462.FStar_Syntax_Syntax.lbpos})))))))
in (mk1 (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs1))), (body1)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (bs, ps)) -> begin
(

let uu____3514 = (

let uu____3515 = (

let uu____3522 = (subst' s t0)
in (

let uu____3525 = (

let uu____3526 = (

let uu____3547 = (FStar_List.map (subst' s) bs)
in (

let uu____3556 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in ((uu____3547), (uu____3556))))
in FStar_Syntax_Syntax.Meta_pattern (uu____3526))
in ((uu____3522), (uu____3525))))
in FStar_Syntax_Syntax.Tm_meta (uu____3515))
in (mk1 uu____3514))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) -> begin
(

let uu____3638 = (

let uu____3639 = (

let uu____3646 = (subst' s t0)
in (

let uu____3649 = (

let uu____3650 = (

let uu____3657 = (subst' s t1)
in ((m), (uu____3657)))
in FStar_Syntax_Syntax.Meta_monadic (uu____3650))
in ((uu____3646), (uu____3649))))
in FStar_Syntax_Syntax.Tm_meta (uu____3639))
in (mk1 uu____3638))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) -> begin
(

let uu____3676 = (

let uu____3677 = (

let uu____3684 = (subst' s t0)
in (

let uu____3687 = (

let uu____3688 = (

let uu____3697 = (subst' s t1)
in ((m1), (m2), (uu____3697)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____3688))
in ((uu____3684), (uu____3687))))
in FStar_Syntax_Syntax.Tm_meta (uu____3677))
in (mk1 uu____3676))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____3712 = (

let uu____3713 = (

let uu____3720 = (subst' s tm)
in ((uu____3720), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____3713))
in (mk1 uu____3712))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted (subst' s) qi)
in (mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi1))))))
end)
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____3734 = (

let uu____3735 = (

let uu____3742 = (subst' s t1)
in ((uu____3742), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____3735))
in (mk1 uu____3734))
end)))


let rec compress_slow : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let t1 = (try_read_memo t)
in (

let t2 = (force_uvar t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed ((t', s), memo) -> begin
((

let uu____3809 = (

let uu____3814 = (push_subst s t')
in FStar_Pervasives_Native.Some (uu____3814))
in (FStar_ST.op_Colon_Equals memo uu____3809));
(compress_slow t2);
)
end
| uu____3846 -> begin
t2
end))))


let compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____3853, uu____3854) -> begin
(compress_slow t)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3891, uu____3892) -> begin
(compress_slow t)
end
| uu____3909 -> begin
t
end))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (

let uu____3944 = (

let uu____3945 = (

let uu____3946 = (

let uu____3947 = (FStar_Range.use_range r)
in (FStar_Range.set_def_range r uu____3947))
in FStar_Syntax_Syntax.SomeUseRange (uu____3946))
in (([]), (uu____3945)))
in (subst' uu____3944 t)))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) t))


let subst_imp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.aqual  ->  FStar_Syntax_Syntax.aqual = (fun s imp -> (subst_imp' (((s)::[]), (FStar_Syntax_Syntax.NoUseRange)) imp))


let closing_subst : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun bs -> (

let uu____4008 = (FStar_List.fold_right (fun uu____4035 uu____4036 -> (match (((uu____4035), (uu____4036))) with
| ((x, uu____4071), (subst1, n1)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n1))))::subst1), ((n1 + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____4008 FStar_Pervasives_Native.fst)))


let open_binders' : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.subst_t) = (fun bs -> (

let rec aux = (fun bs1 o -> (match (bs1) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___591_4209 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4210 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___591_4209.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___591_4209.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4210}))
in (

let imp1 = (subst_imp o imp)
in (

let o1 = (

let uu____4217 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4217)
in (

let uu____4223 = (aux bs' o1)
in (match (uu____4223) with
| (bs'1, o2) -> begin
(((((x'), (imp1)))::bs'1), (o2))
end)))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____4284 = (open_binders' bs)
in (FStar_Pervasives_Native.fst uu____4284)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____4306 = (open_binders' bs)
in (match (uu____4306) with
| (bs', opening) -> begin
(

let uu____4319 = (subst opening t)
in ((bs'), (uu____4319), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____4335 = (open_term' bs t)
in (match (uu____4335) with
| (b, t1, uu____4348) -> begin
((b), (t1))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____4364 = (open_binders' bs)
in (match (uu____4364) with
| (bs', opening) -> begin
(

let uu____4375 = (subst_comp opening t)
in ((bs'), (uu____4375)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec open_pat_aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____4425) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4450 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____4521 uu____4522 -> (match (((uu____4521), (uu____4522))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____4636 = (open_pat_aux sub2 p2)
in (match (uu____4636) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____4450) with
| (pats1, sub2) -> begin
(((

let uu___638_4746 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___638_4746.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___642_4767 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4768 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___642_4767.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___642_4767.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4768}))
in (

let sub2 = (

let uu____4774 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4774)
in (((

let uu___646_4785 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.p = uu___646_4785.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___650_4790 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____4791 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___650_4790.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___650_4790.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4791}))
in (

let sub2 = (

let uu____4797 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____4797)
in (((

let uu___654_4808 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.p = uu___654_4808.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___660_4818 = x
in (

let uu____4819 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___660_4818.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___660_4818.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4819}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___664_4828 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___664_4828.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (open_pat_aux [] p)))


let open_branch' : FStar_Syntax_Syntax.branch  ->  (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t) = (fun uu____4842 -> (match (uu____4842) with
| (p, wopt, e) -> begin
(

let uu____4866 = (open_pat p)
in (match (uu____4866) with
| (p1, opening) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____4895 = (subst opening w)
in FStar_Pervasives_Native.Some (uu____4895))
end)
in (

let e1 = (subst opening e)
in ((((p1), (wopt1), (e1))), (opening))))
end))
end))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun br -> (

let uu____4915 = (open_branch' br)
in (match (uu____4915) with
| (br1, uu____4921) -> begin
br1
end)))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____4933 = (closing_subst bs)
in (subst uu____4933 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____4947 = (closing_subst bs)
in (subst_comp uu____4947 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs1 -> (match (bs1) with
| [] -> begin
[]
end
| ((x, imp))::tl1 -> begin
(

let x1 = (

let uu___696_5015 = x
in (

let uu____5016 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___696_5015.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___696_5015.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5016}))
in (

let imp1 = (subst_imp s imp)
in (

let s' = (

let uu____5023 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5023)
in (

let uu____5029 = (aux s' tl1)
in (((x1), (imp1)))::uu____5029))))
end))
in (aux [] bs)))


let close_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____5093) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____5118 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____5189 uu____5190 -> (match (((uu____5189), (uu____5190))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____5304 = (aux sub2 p2)
in (match (uu____5304) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____5118) with
| (pats1, sub2) -> begin
(((

let uu___723_5414 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___723_5414.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___727_5435 = x
in (

let uu____5436 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___727_5435.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___727_5435.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5436}))
in (

let sub2 = (

let uu____5442 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5442)
in (((

let uu___731_5453 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___731_5453.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___735_5458 = x
in (

let uu____5459 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___735_5458.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___735_5458.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5459}))
in (

let sub2 = (

let uu____5465 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____5465)
in (((

let uu___739_5476 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___739_5476.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___745_5486 = x
in (

let uu____5487 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___745_5486.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___745_5486.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5487}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___749_5496 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.p = uu___749_5496.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____5506 -> (match (uu____5506) with
| (p, wopt, e) -> begin
(

let uu____5526 = (close_pat p)
in (match (uu____5526) with
| (p1, closing) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____5563 = (subst closing w)
in FStar_Pervasives_Native.Some (uu____5563))
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

let uu____5651 = (univ_var_opening us)
in (match (uu____5651) with
| (s, us') -> begin
(

let t1 = (subst s t)
in ((us'), (t1)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____5694 = (univ_var_opening us)
in (match (uu____5694) with
| (s, us') -> begin
(

let uu____5717 = (subst_comp s c)
in ((us'), (uu____5717)))
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

let uu____5780 = (

let uu____5792 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5792) with
| true -> begin
(((Prims.parse_int "0")), (lbs), ([]))
end
| uu____5812 -> begin
(FStar_List.fold_right (fun lb uu____5832 -> (match (uu____5832) with
| (i, lbs1, out) -> begin
(

let x = (

let uu____5869 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____5869))
in (((i + (Prims.parse_int "1"))), (((

let uu___801_5877 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___801_5877.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___801_5877.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___801_5877.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___801_5877.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___801_5877.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___801_5877.FStar_Syntax_Syntax.lbpos}))::lbs1), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
end))
in (match (uu____5780) with
| (n_let_recs, lbs1, let_rec_opening) -> begin
(

let lbs2 = (FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let uu____5920 = (FStar_List.fold_right (fun u uu____5950 -> (match (uu____5950) with
| (i, us, out) -> begin
(

let u1 = (FStar_Syntax_Syntax.new_univ_name FStar_Pervasives_Native.None)
in (((i + (Prims.parse_int "1"))), ((u1)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u1)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____5920) with
| (uu____5999, us, u_let_rec_opening) -> begin
(

let uu___818_6012 = lb
in (

let uu____6013 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____6016 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___818_6012.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu____6013; FStar_Syntax_Syntax.lbeff = uu___818_6012.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____6016; FStar_Syntax_Syntax.lbattrs = uu___818_6012.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___818_6012.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_opening t)
in ((lbs2), (t1))))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____6043 = (

let uu____6051 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____6051) with
| true -> begin
(((Prims.parse_int "0")), ([]))
end
| uu____6065 -> begin
(FStar_List.fold_right (fun lb uu____6080 -> (match (uu____6080) with
| (i, out) -> begin
(

let uu____6103 = (

let uu____6106 = (

let uu____6107 = (

let uu____6113 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____6113), (i)))
in FStar_Syntax_Syntax.NM (uu____6107))
in (uu____6106)::out)
in (((i + (Prims.parse_int "1"))), (uu____6103)))
end)) lbs (((Prims.parse_int "0")), ([])))
end))
in (match (uu____6043) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____6152 = (FStar_List.fold_right (fun u uu____6172 -> (match (uu____6172) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____6152) with
| (uu____6203, u_let_rec_closing) -> begin
(

let uu___840_6211 = lb
in (

let uu____6212 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____6215 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___840_6211.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___840_6211.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____6212; FStar_Syntax_Syntax.lbeff = uu___840_6211.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____6215; FStar_Syntax_Syntax.lbattrs = uu___840_6211.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___840_6211.FStar_Syntax_Syntax.lbpos})))
end)))))
in (

let t1 = (subst let_rec_closing t)
in ((lbs1), (t1))))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____6231 -> (match (uu____6231) with
| (us, t) -> begin
(

let n1 = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____6266 -> (match (uu____6266) with
| (x, uu____6275) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n1 - i)))))
end)) binders)
in (

let t1 = (subst s t)
in ((us), (t1))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____6296 -> (match (uu____6296) with
| (us', t) -> begin
(

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n1 - i)))))) us)
in (

let uu____6320 = (subst s t)
in ((us'), (uu____6320))))))
end))


let subst_tscheme : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun s uu____6339 -> (match (uu____6339) with
| (us, t) -> begin
(

let s1 = (shift_subst (FStar_List.length us) s)
in (

let uu____6353 = (subst s1 t)
in ((us), (uu____6353))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n1 = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____6394 -> (match (uu____6394) with
| (x, uu____6403) -> begin
FStar_Syntax_Syntax.DB ((((n1 - i)), (x)))
end))))))


let closing_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (closing_subst bs))


let open_term_1 : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term) = (fun b t -> (

let uu____6430 = (open_term ((b)::[]) t)
in (match (uu____6430) with
| ((b1)::[], t1) -> begin
((b1), (t1))
end
| uu____6471 -> begin
(failwith "impossible: open_term_1")
end)))


let open_term_bvs : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun bvs t -> (

let uu____6502 = (

let uu____6507 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (open_term uu____6507 t))
in (match (uu____6502) with
| (bs, t1) -> begin
(

let uu____6522 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in ((uu____6522), (t1)))
end)))


let open_term_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun bv t -> (

let uu____6550 = (open_term_bvs ((bv)::[]) t)
in (match (uu____6550) with
| ((bv1)::[], t1) -> begin
((bv1), (t1))
end
| uu____6565 -> begin
(failwith "impossible: open_term_bv")
end)))




