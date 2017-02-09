
open Prims

let subst_to_string = (fun s -> (

let uu____14 = (FStar_All.pipe_right s (FStar_List.map (fun uu____22 -> (match (uu____22) with
| (b, uu____26) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right uu____14 (FStar_String.concat ", "))))


let rec apply_until_some = (fun f s -> (match (s) with
| [] -> begin
None
end
| (s0)::rest -> begin
(

let uu____61 = (f s0)
in (match (uu____61) with
| None -> begin
(apply_until_some f rest)
end
| Some (st) -> begin
Some (((rest), (st)))
end))
end))


let map_some_curry = (fun f x uu___100_101 -> (match (uu___100_101) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map = (fun f s g t -> (

let uu____162 = (apply_until_some f s)
in (FStar_All.pipe_right uu____162 (map_some_curry g t))))


let compose_subst = (fun s1 s2 -> (

let s = (FStar_List.append (Prims.fst s1) (Prims.fst s2))
in (

let ropt = (match ((Prims.snd s2)) with
| Some (uu____217) -> begin
(Prims.snd s2)
end
| uu____220 -> begin
(Prims.snd s1)
end)
in ((s), (ropt)))))


let delay : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  FStar_Syntax_Syntax.term = (fun t s -> (match (t.FStar_Syntax_Syntax.n) with
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
(delay t' (([]), (Some (t.FStar_Syntax_Syntax.pos))))
end))))


let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(

let uu____450 = (FStar_ST.read m)
in (match (uu____450) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(

let t' = (

let uu____486 = (c ())
in (force_delayed_thunk uu____486))
in ((FStar_ST.write m (Some (t')));
t';
))
end
| uu____497 -> begin
t
end)
end
| Some (t') -> begin
(

let t' = (force_delayed_thunk t')
in ((FStar_ST.write m (Some (t')));
t';
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
| Some (u) -> begin
(compress_univ u)
end
| uu____540 -> begin
u
end))
end
| uu____542 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun uu___101_552 -> (match (uu___101_552) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(

let uu____556 = (

let uu____557 = (

let uu____558 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x uu____558))
in (FStar_Syntax_Syntax.bv_to_name uu____557))
in Some (uu____556))
end
| uu____559 -> begin
None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun uu___102_569 -> (match (uu___102_569) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____573 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___107_574 = a
in {FStar_Syntax_Syntax.ppname = uu___107_574.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___107_574.FStar_Syntax_Syntax.sort}))
in Some (uu____573))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| uu____583 -> begin
None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun uu___103_593 -> (match (uu___103_593) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| uu____597 -> begin
None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun uu___104_607 -> (match (uu___104_607) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____611 -> begin
None
end))))


let rec subst_univ : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun s u -> (

let u = (compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(apply_until_some_then_map (subst_univ_bv x) s subst_univ u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(apply_until_some_then_map (subst_univ_nm x) s subst_univ u)
end
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_unif (_)) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(

let uu____629 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (uu____629))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____632 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (uu____632))
end)))


let tag_with_range = (fun t s -> (match ((Prims.snd s)) with
| None -> begin
t
end
| Some (r) -> begin
(

let r = (FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r)
in (

let t' = (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____665 = (FStar_Syntax_Syntax.set_range_of_bv bv r)
in FStar_Syntax_Syntax.Tm_bvar (uu____665))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____667 = (FStar_Syntax_Syntax.set_range_of_bv bv r)
in FStar_Syntax_Syntax.Tm_name (uu____667))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v = (

let uu___108_675 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r); FStar_Syntax_Syntax.ty = uu___108_675.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___108_675.FStar_Syntax_Syntax.p})
in (

let fv = (

let uu___109_691 = fv
in {FStar_Syntax_Syntax.fv_name = v; FStar_Syntax_Syntax.fv_delta = uu___109_691.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___109_691.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv))))
end
| t' -> begin
t'
end)
in (

let uu___110_693 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.tk = uu___110_693.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___110_693.FStar_Syntax_Syntax.vars})))
end))


let tag_lid_with_range = (fun l s -> (match ((Prims.snd s)) with
| None -> begin
l
end
| Some (r) -> begin
(

let uu____720 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r)
in (FStar_Ident.set_lid_range l uu____720))
end))


let mk_range : FStar_Range.range  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Range.range = (fun r s -> (match ((Prims.snd s)) with
| None -> begin
r
end
| Some (r') -> begin
(FStar_Range.set_use_range r r')
end))


let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (

let subst_tail = (fun tl -> (subst' ((tl), ((Prims.snd s)))))
in (match (s) with
| (([], None)) | ((([])::[], None)) -> begin
t
end
| uu____802 -> begin
(

let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t'), ((compose_subst s' s))))) t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (uu____883), uu____884) -> begin
(failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) (Prims.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) (Prims.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____940 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (

let uu____941 = (

let uu____944 = (

let uu____945 = (subst_univ (Prims.fst s) u)
in FStar_Syntax_Syntax.Tm_type (uu____945))
in (FStar_Syntax_Syntax.mk uu____944))
in (uu____941 None uu____940)))
end
| uu____957 -> begin
(

let uu____958 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t0), (s)))) uu____958))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___105_972 -> (match (uu___105_972) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(

let uu____976 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (uu____976))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| (([], None)) | ((([])::[], None)) -> begin
t
end
| uu____996 -> begin
(

let uu___111_1002 = t
in (

let uu____1003 = (FStar_List.map (subst_univ (Prims.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____1007 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____1010 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____1013 = (FStar_List.map (fun uu____1027 -> (match (uu____1027) with
| (t, imp) -> begin
(

let uu____1042 = (subst' s t)
in ((uu____1042), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (

let uu____1047 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu____1003; FStar_Syntax_Syntax.effect_name = uu____1007; FStar_Syntax_Syntax.result_typ = uu____1010; FStar_Syntax_Syntax.effect_args = uu____1013; FStar_Syntax_Syntax.flags = uu____1047}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| (([], None)) | ((([])::[], None)) -> begin
t
end
| uu____1069 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____1085 = (subst' s t)
in (

let uu____1086 = (FStar_Option.map (subst_univ (Prims.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____1085 uu____1086)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____1099 = (subst' s t)
in (

let uu____1100 = (FStar_Option.map (subst_univ (Prims.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1099 uu____1100)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1106 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp uu____1106))
end)
end))


let shift : Prims.int  ->  FStar_Syntax_Syntax.subst_elt  ->  FStar_Syntax_Syntax.subst_elt = (fun n s -> (match (s) with
| FStar_Syntax_Syntax.DB (i, t) -> begin
FStar_Syntax_Syntax.DB ((((i + n)), (t)))
end
| FStar_Syntax_Syntax.UN (i, t) -> begin
FStar_Syntax_Syntax.UN ((((i + n)), (t)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
FStar_Syntax_Syntax.NM (((x), ((i + n))))
end
| FStar_Syntax_Syntax.UD (x, i) -> begin
FStar_Syntax_Syntax.UD (((x), ((i + n))))
end
| FStar_Syntax_Syntax.NT (uu____1121) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))


let shift_subst' = (fun n s -> (

let uu____1153 = (FStar_All.pipe_right (Prims.fst s) (FStar_List.map (shift_subst n)))
in ((uu____1153), ((Prims.snd s)))))


let subst_binder' = (fun s uu____1175 -> (match (uu____1175) with
| (x, imp) -> begin
(

let uu____1180 = (

let uu___112_1181 = x
in (

let uu____1182 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___112_1181.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___112_1181.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1182}))
in ((uu____1180), (imp)))
end))


let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((i = (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1222 -> begin
(

let uu____1223 = (shift_subst' i s)
in (subst_binder' uu____1223 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (None)) bs))


let subst_arg' = (fun s uu____1257 -> (match (uu____1257) with
| (t, imp) -> begin
(

let uu____1268 = (subst' s t)
in ((uu____1268), (imp)))
end))


let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range Prims.option)  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (uu____1343) -> begin
((p), (n))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let uu____1355 = (aux n p)
in (match (uu____1355) with
| (p, m) -> begin
(

let ps = (FStar_List.map (fun p -> (

let uu____1369 = (aux n p)
in (Prims.fst uu____1369))) ps)
in (((

let uu___113_1374 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = uu___113_1374.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___113_1374.FStar_Syntax_Syntax.p})), (m)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1387 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1412 uu____1413 -> (match (((uu____1412), (uu____1413))) with
| ((pats, n), (p, imp)) -> begin
(

let uu____1460 = (aux n p)
in (match (uu____1460) with
| (p, m) -> begin
(((((p), (imp)))::pats), (m))
end))
end)) (([]), (n))))
in (match (uu____1387) with
| (pats, n) -> begin
(((

let uu___114_1492 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = uu___114_1492.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___114_1492.FStar_Syntax_Syntax.p})), (n))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let uu___115_1508 = x
in (

let uu____1509 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___115_1508.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_1508.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1509}))
in (((

let uu___116_1514 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = uu___116_1514.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___116_1514.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let uu___117_1525 = x
in (

let uu____1526 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___117_1525.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___117_1525.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1526}))
in (((

let uu___118_1531 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = uu___118_1531.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___118_1531.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let uu___119_1547 = x
in (

let uu____1548 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___119_1547.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___119_1547.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1548}))
in (

let t0 = (subst' s t0)
in (((

let uu___120_1556 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = uu___120_1556.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___120_1556.FStar_Syntax_Syntax.p})), (n)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (l)) -> begin
(

let uu____1590 = (

let uu____1593 = (

let uu___121_1594 = l
in (

let uu____1595 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___121_1594.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____1595; FStar_Syntax_Syntax.cflags = uu___121_1594.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____1598 -> (

let uu____1599 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s uu____1599)))}))
in FStar_Util.Inl (uu____1593))
in Some (uu____1590))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk = (fun t' -> (

let uu____1622 = (mk_range t.FStar_Syntax_Syntax.pos s)
in ((FStar_Syntax_Syntax.mk t') None uu____1622)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1633) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
(tag_with_range t s)
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us = (FStar_List.map (subst_univ (Prims.fst s)) us)
in (

let uu____1675 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us)
in (tag_with_range uu____1675 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(

let uu____1696 = (

let uu____1697 = (

let uu____1707 = (subst' s t0)
in (

let uu____1710 = ((subst_args' s) args)
in ((uu____1707), (uu____1710))))
in FStar_Syntax_Syntax.Tm_app (uu____1697))
in (mk uu____1696))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inl (t1), lopt) -> begin
(

let uu____1744 = (

let uu____1745 = (

let uu____1758 = (subst' s t0)
in (

let uu____1761 = (

let uu____1768 = (subst' s t1)
in FStar_Util.Inl (uu____1768))
in ((uu____1758), (uu____1761), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____1745))
in (mk uu____1744))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inr (c), lopt) -> begin
(

let uu____1805 = (

let uu____1806 = (

let uu____1819 = (subst' s t0)
in (

let uu____1822 = (

let uu____1829 = (subst_comp' s c)
in FStar_Util.Inr (uu____1829))
in ((uu____1819), (uu____1822), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____1806))
in (mk uu____1805))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n = (FStar_List.length bs)
in (

let s' = (shift_subst' n s)
in (

let uu____1882 = (

let uu____1883 = (

let uu____1898 = (subst_binders' s bs)
in (

let uu____1902 = (subst' s' body)
in (

let uu____1905 = (push_subst_lcomp s' lopt)
in ((uu____1898), (uu____1902), (uu____1905)))))
in FStar_Syntax_Syntax.Tm_abs (uu____1883))
in (mk uu____1882))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n = (FStar_List.length bs)
in (

let uu____1942 = (

let uu____1943 = (

let uu____1951 = (subst_binders' s bs)
in (

let uu____1955 = (

let uu____1958 = (shift_subst' n s)
in (subst_comp' uu____1958 comp))
in ((uu____1951), (uu____1955))))
in FStar_Syntax_Syntax.Tm_arrow (uu____1943))
in (mk uu____1942)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x = (

let uu___122_1979 = x
in (

let uu____1980 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___122_1979.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___122_1979.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1980}))
in (

let phi = (

let uu____1986 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____1986 phi))
in (mk (FStar_Syntax_Syntax.Tm_refine (((x), (phi)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t0 = (subst' s t0)
in (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun uu____2069 -> (match (uu____2069) with
| (pat, wopt, branch) -> begin
(

let uu____2105 = (subst_pat' s pat)
in (match (uu____2105) with
| (pat, n) -> begin
(

let s = (shift_subst' n s)
in (

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____2140 = (subst' s w)
in Some (uu____2140))
end)
in (

let branch = (subst' s branch)
in ((pat), (wopt), (branch)))))
end))
end))))
in (mk (FStar_Syntax_Syntax.Tm_match (((t0), (pats)))))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body) -> begin
(

let n = (FStar_List.length lbs)
in (

let sn = (shift_subst' n s)
in (

let body = (subst' sn body)
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let lbt = (subst' s lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbd = (

let uu____2200 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____2200) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____2203 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___123_2210 = x
in {FStar_Syntax_Syntax.ppname = uu___123_2210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_2210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((

let uu___124_2212 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___125_2213 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___125_2213.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = uu___125_2213.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___124_2212.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___124_2212.FStar_Syntax_Syntax.fv_qual}))
end)
in (

let uu___126_2228 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___126_2228.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___126_2228.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (mk (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs))), (body)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let uu____2247 = (

let uu____2248 = (

let uu____2253 = (subst' s t0)
in (

let uu____2256 = (

let uu____2257 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____2257))
in ((uu____2253), (uu____2256))))
in FStar_Syntax_Syntax.Tm_meta (uu____2248))
in (mk uu____2247))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t)) -> begin
(

let uu____2299 = (

let uu____2300 = (

let uu____2305 = (subst' s t0)
in (

let uu____2308 = (

let uu____2309 = (

let uu____2314 = (subst' s t)
in ((m), (uu____2314)))
in FStar_Syntax_Syntax.Meta_monadic (uu____2309))
in ((uu____2305), (uu____2308))))
in FStar_Syntax_Syntax.Tm_meta (uu____2300))
in (mk uu____2299))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t)) -> begin
(

let uu____2333 = (

let uu____2334 = (

let uu____2339 = (subst' s t0)
in (

let uu____2342 = (

let uu____2343 = (

let uu____2349 = (subst' s t)
in ((m1), (m2), (uu____2349)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____2343))
in ((uu____2339), (uu____2342))))
in FStar_Syntax_Syntax.Tm_meta (uu____2334))
in (mk uu____2333))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(

let uu____2362 = (

let uu____2363 = (

let uu____2368 = (subst' s t)
in ((uu____2368), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____2363))
in (mk uu____2362))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(

let t' = (

let uu____2431 = (push_subst s t)
in (compress uu____2431))
in ((FStar_Unionfind.update_in_tx memo (Some (t')));
t';
))
end
| uu____2438 -> begin
(

let t' = (force_uvar t)
in (match (t'.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2442) -> begin
(compress t')
end
| uu____2463 -> begin
t'
end))
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (subst' (([]), (Some ((

let uu___127_2487 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = uu___127_2487.FStar_Range.use_range})))) t))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (None)) t))


let closing_subst = (fun bs -> (

let uu____2515 = (FStar_List.fold_right (fun uu____2524 uu____2525 -> (match (((uu____2524), (uu____2525))) with
| ((x, uu____2540), (subst, n)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n))))::subst), ((n + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____2515 Prims.fst)))


let open_binders' = (fun bs -> (

let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___128_2620 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____2621 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___128_2620.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___128_2620.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2621}))
in (

let o = (

let uu____2626 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____2626)
in (

let uu____2628 = (aux bs' o)
in (match (uu____2628) with
| (bs', o) -> begin
(((((x'), (imp)))::bs'), (o))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____2660 = (open_binders' bs)
in (Prims.fst uu____2660)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____2680 = (open_binders' bs)
in (match (uu____2680) with
| (bs', opening) -> begin
(

let uu____2700 = (subst opening t)
in ((bs'), (uu____2700), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____2713 = (open_term' bs t)
in (match (uu____2713) with
| (b, t, uu____2721) -> begin
((b), (t))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____2730 = (open_binders' bs)
in (match (uu____2730) with
| (bs', opening) -> begin
(

let uu____2749 = (subst_comp opening t)
in ((bs'), (uu____2749)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec aux_disj = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____2786) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (uu____2792) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu___129_2805 = p
in (

let uu____2808 = (

let uu____2809 = (

let uu____2817 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____2841 -> (match (uu____2841) with
| (p, b) -> begin
(

let uu____2856 = (aux_disj sub renaming p)
in ((uu____2856), (b)))
end))))
in ((fv), (uu____2817)))
in FStar_Syntax_Syntax.Pat_cons (uu____2809))
in {FStar_Syntax_Syntax.v = uu____2808; FStar_Syntax_Syntax.ty = uu___129_2805.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___129_2805.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let yopt = (FStar_Util.find_map renaming (fun uu___106_2871 -> (match (uu___106_2871) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| uu____2877 -> begin
None
end)))
in (

let y = (match (yopt) with
| None -> begin
(

let uu___130_2881 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____2882 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___130_2881.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___130_2881.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2882}))
end
| Some (y) -> begin
y
end)
in (

let uu___131_2886 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = uu___131_2886.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___131_2886.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___132_2891 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____2892 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___132_2891.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___132_2891.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2892}))
in (

let uu___133_2895 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = uu___133_2895.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___133_2895.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let uu___134_2905 = x
in (

let uu____2906 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___134_2905.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___134_2905.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2906}))
in (

let t0 = (subst sub t0)
in (

let uu___135_2910 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = uu___135_2910.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___135_2910.FStar_Syntax_Syntax.p})))
end))
in (

let rec aux = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (uu____2964) -> begin
((p), (sub), (renaming))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let uu____2980 = (aux sub renaming p)
in (match (uu____2980) with
| (p, sub, renaming) -> begin
(

let ps = (FStar_List.map (aux_disj sub renaming) ps)
in (((

let uu___136_3028 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = uu___136_3028.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___136_3028.FStar_Syntax_Syntax.p})), (sub), (renaming)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3045 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____3091 uu____3092 -> (match (((uu____3091), (uu____3092))) with
| ((pats, sub, renaming), (p, imp)) -> begin
(

let uu____3180 = (aux sub renaming p)
in (match (uu____3180) with
| (p, sub, renaming) -> begin
(((((p), (imp)))::pats), (sub), (renaming))
end))
end)) (([]), (sub), (renaming))))
in (match (uu____3045) with
| (pats, sub, renaming) -> begin
(((

let uu___137_3281 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = uu___137_3281.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___137_3281.FStar_Syntax_Syntax.p})), (sub), (renaming))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___138_3295 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____3296 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___138_3295.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___138_3295.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3296}))
in (

let sub = (

let uu____3301 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____3301)
in (((

let uu___139_3309 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = uu___139_3309.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___139_3309.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___140_3316 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____3317 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___140_3316.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___140_3316.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3317}))
in (

let sub = (

let uu____3322 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____3322)
in (((

let uu___141_3330 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = uu___141_3330.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___141_3330.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let uu___142_3342 = x
in (

let uu____3343 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___142_3342.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___142_3342.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3343}))
in (

let t0 = (subst sub t0)
in (((

let uu___143_3353 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = uu___143_3353.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___143_3353.FStar_Syntax_Syntax.p})), (sub), (renaming))))
end))
in (

let uu____3356 = (aux [] [] p)
in (match (uu____3356) with
| (p, sub, uu____3372) -> begin
((p), (sub))
end)))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____3390 -> (match (uu____3390) with
| (p, wopt, e) -> begin
(

let uu____3408 = (open_pat p)
in (match (uu____3408) with
| (p, opening) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____3423 = (subst opening w)
in Some (uu____3423))
end)
in (

let e = (subst opening e)
in ((p), (wopt), (e))))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____3432 = (closing_subst bs)
in (subst uu____3432 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____3440 = (closing_subst bs)
in (subst_comp uu____3440 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| ((x, imp))::tl -> begin
(

let x = (

let uu___144_3473 = x
in (

let uu____3474 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___144_3473.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___144_3473.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3474}))
in (

let s' = (

let uu____3479 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::uu____3479)
in (

let uu____3481 = (aux s' tl)
in (((x), (imp)))::uu____3481)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let uu___145_3495 = lc
in (

let uu____3496 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___145_3495.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____3496; FStar_Syntax_Syntax.cflags = uu___145_3495.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____3499 -> (

let uu____3500 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s uu____3500)))}))))


let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (uu____3543) -> begin
((p), (sub))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let uu____3556 = (aux sub p)
in (match (uu____3556) with
| (p, sub) -> begin
(

let ps = (FStar_List.map (fun p -> (

let uu____3586 = (aux sub p)
in (Prims.fst uu____3586))) ps)
in (((

let uu___146_3598 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = uu___146_3598.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___146_3598.FStar_Syntax_Syntax.p})), (sub)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3615 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____3649 uu____3650 -> (match (((uu____3649), (uu____3650))) with
| ((pats, sub), (p, imp)) -> begin
(

let uu____3715 = (aux sub p)
in (match (uu____3715) with
| (p, sub) -> begin
(((((p), (imp)))::pats), (sub))
end))
end)) (([]), (sub))))
in (match (uu____3615) with
| (pats, sub) -> begin
(((

let uu___147_3781 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = uu___147_3781.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___147_3781.FStar_Syntax_Syntax.p})), (sub))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let uu___148_3795 = x
in (

let uu____3796 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___148_3795.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___148_3795.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3796}))
in (

let sub = (

let uu____3801 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::uu____3801)
in (((

let uu___149_3806 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = uu___149_3806.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___149_3806.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let uu___150_3811 = x
in (

let uu____3812 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___150_3811.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_3811.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3812}))
in (

let sub = (

let uu____3817 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::uu____3817)
in (((

let uu___151_3822 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = uu___151_3822.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___151_3822.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let uu___152_3832 = x
in (

let uu____3833 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___152_3832.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___152_3832.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3833}))
in (

let t0 = (subst sub t0)
in (((

let uu___153_3840 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = uu___153_3840.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___153_3840.FStar_Syntax_Syntax.p})), (sub))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____3845 -> (match (uu____3845) with
| (p, wopt, e) -> begin
(

let uu____3863 = (close_pat p)
in (match (uu____3863) with
| (p, closing) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____3887 = (subst closing w)
in Some (uu____3887))
end)
in (

let e = (subst closing e)
in ((p), (wopt), (e))))
end))
end))


let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let uu____3903 = (

let uu____3908 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (

let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in ((FStar_Syntax_Syntax.UN ((((n - i)), (FStar_Syntax_Syntax.U_name (u'))))), (u'))))))
in (FStar_All.pipe_right uu____3908 FStar_List.unzip))
in (match (uu____3903) with
| (s, us') -> begin
((s), (us'))
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (

let uu____3949 = (univ_var_opening us)
in (match (uu____3949) with
| (s, us') -> begin
(

let t = (subst s t)
in ((us'), (t)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____3974 = (univ_var_opening us)
in (match (uu____3974) with
| (s, us') -> begin
(

let uu____3987 = (subst_comp s c)
in ((us'), (uu____3987)))
end)))


let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun us t -> (

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD (((u), ((n - i)))))))
in (subst s t))))


let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun us c -> (

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD (((u), ((n - i)))))))
in (subst_comp s c))))


let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____4030 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____4030) with
| true -> begin
((lbs), (t))
end
| uu____4035 -> begin
(

let uu____4036 = (FStar_List.fold_right (fun lb uu____4048 -> (match (uu____4048) with
| (i, lbs, out) -> begin
(

let x = (

let uu____4067 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____4067))
in (((i + (Prims.parse_int "1"))), (((

let uu___154_4070 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___154_4070.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___154_4070.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___154_4070.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___154_4070.FStar_Syntax_Syntax.lbdef}))::lbs), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
in (match (uu____4036) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____4088 = (FStar_List.fold_right (fun u uu____4100 -> (match (uu____4100) with
| (i, us, out) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name None)
in (((i + (Prims.parse_int "1"))), ((u)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____4088) with
| (uu____4123, us, u_let_rec_opening) -> begin
(

let uu___155_4130 = lb
in (

let uu____4131 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___155_4130.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu___155_4130.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___155_4130.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____4131}))
end)))))
in (

let t = (subst let_rec_opening t)
in ((lbs), (t))))
end))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____4147 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____4147) with
| true -> begin
((lbs), (t))
end
| uu____4152 -> begin
(

let uu____4153 = (FStar_List.fold_right (fun lb uu____4161 -> (match (uu____4161) with
| (i, out) -> begin
(

let uu____4172 = (

let uu____4174 = (

let uu____4175 = (

let uu____4178 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____4178), (i)))
in FStar_Syntax_Syntax.NM (uu____4175))
in (uu____4174)::out)
in (((i + (Prims.parse_int "1"))), (uu____4172)))
end)) lbs (((Prims.parse_int "0")), ([])))
in (match (uu____4153) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____4193 = (FStar_List.fold_right (fun u uu____4201 -> (match (uu____4201) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____4193) with
| (uu____4214, u_let_rec_closing) -> begin
(

let uu___156_4218 = lb
in (

let uu____4219 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___156_4218.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___156_4218.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___156_4218.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___156_4218.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____4219}))
end)))))
in (

let t = (subst let_rec_closing t)
in ((lbs), (t))))
end))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____4229 -> (match (uu____4229) with
| (us, t) -> begin
(

let n = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____4247 -> (match (uu____4247) with
| (x, uu____4251) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n - i)))))
end)) binders)
in (

let t = (subst s t)
in ((us), (t))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____4262 -> (match (uu____4262) with
| (us', t) -> begin
(

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n - i)))))) us)
in (

let uu____4280 = (subst s t)
in ((us'), (uu____4280))))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____4295 -> (match (uu____4295) with
| (x, uu____4299) -> begin
FStar_Syntax_Syntax.DB ((((n - i)), (x)))
end))))))




