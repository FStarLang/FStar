
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


let map_some_curry = (fun f x uu___98_101 -> (match (uu___98_101) with
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

let t'1 = (force_delayed_thunk t')
in ((FStar_ST.write m (Some (t'1)));
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
| Some (u1) -> begin
(compress_univ u1)
end
| uu____540 -> begin
u
end))
end
| uu____542 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun uu___99_552 -> (match (uu___99_552) with
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


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun uu___100_569 -> (match (uu___100_569) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(

let uu____573 = (FStar_Syntax_Syntax.bv_to_tm (

let uu___105_574 = a
in {FStar_Syntax_Syntax.ppname = uu___105_574.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___105_574.FStar_Syntax_Syntax.sort}))
in Some (uu____573))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| uu____583 -> begin
None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun uu___101_593 -> (match (uu___101_593) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| uu____597 -> begin
None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun uu___102_607 -> (match (uu___102_607) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____611 -> begin
None
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
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_unif (_)) -> begin
u1
end
| FStar_Syntax_Syntax.U_succ (u2) -> begin
(

let uu____629 = (subst_univ s u2)
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

let r1 = (FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r)
in (

let t' = (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____665 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_bvar (uu____665))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____667 = (FStar_Syntax_Syntax.set_range_of_bv bv r1)
in FStar_Syntax_Syntax.Tm_name (uu____667))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v1 = (

let uu___106_675 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1); FStar_Syntax_Syntax.ty = uu___106_675.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___106_675.FStar_Syntax_Syntax.p})
in (

let fv1 = (

let uu___107_691 = fv
in {FStar_Syntax_Syntax.fv_name = v1; FStar_Syntax_Syntax.fv_delta = uu___107_691.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___107_691.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv1))))
end
| t' -> begin
t'
end)
in (

let uu___108_693 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.tk = uu___108_693.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu___108_693.FStar_Syntax_Syntax.vars})))
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

let subst_tail = (fun tl1 -> (subst' ((tl1), ((Prims.snd s)))))
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
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___103_972 -> (match (uu___103_972) with
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

let uu___109_1002 = t
in (

let uu____1003 = (FStar_List.map (subst_univ (Prims.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (

let uu____1007 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (

let uu____1010 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (

let uu____1013 = (FStar_List.map (fun uu____1027 -> (match (uu____1027) with
| (t1, imp) -> begin
(

let uu____1042 = (subst' s t1)
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
| FStar_Syntax_Syntax.Total (t1, uopt) -> begin
(

let uu____1085 = (subst' s t1)
in (

let uu____1086 = (FStar_Option.map (subst_univ (Prims.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____1085 uu____1086)))
end
| FStar_Syntax_Syntax.GTotal (t1, uopt) -> begin
(

let uu____1099 = (subst' s t1)
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
| FStar_Syntax_Syntax.NT (uu____1121) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n1 s -> (FStar_List.map (shift n1) s))


let shift_subst' = (fun n1 s -> (

let uu____1153 = (FStar_All.pipe_right (Prims.fst s) (FStar_List.map (shift_subst n1)))
in ((uu____1153), ((Prims.snd s)))))


let subst_binder' = (fun s uu____1175 -> (match (uu____1175) with
| (x, imp) -> begin
(

let uu____1180 = (

let uu___110_1181 = x
in (

let uu____1182 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___110_1181.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___110_1181.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1182}))
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

let rec aux = (fun n1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (uu____1343) -> begin
((p1), (n1))
end
| FStar_Syntax_Syntax.Pat_disj ((p2)::ps) -> begin
(

let uu____1355 = (aux n1 p2)
in (match (uu____1355) with
| (p3, m) -> begin
(

let ps1 = (FStar_List.map (fun p4 -> (

let uu____1369 = (aux n1 p4)
in (Prims.fst uu____1369))) ps)
in (((

let uu___111_1374 = p3
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p3)::ps1); FStar_Syntax_Syntax.ty = uu___111_1374.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___111_1374.FStar_Syntax_Syntax.p})), (m)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1387 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1412 uu____1413 -> (match (((uu____1412), (uu____1413))) with
| ((pats1, n2), (p2, imp)) -> begin
(

let uu____1460 = (aux n2 p2)
in (match (uu____1460) with
| (p3, m) -> begin
(((((p3), (imp)))::pats1), (m))
end))
end)) (([]), (n1))))
in (match (uu____1387) with
| (pats1, n2) -> begin
(((

let uu___112_1492 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.ty = uu___112_1492.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___112_1492.FStar_Syntax_Syntax.p})), (n2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___113_1508 = x
in (

let uu____1509 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___113_1508.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___113_1508.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1509}))
in (((

let uu___114_1514 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.ty = uu___114_1514.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___114_1514.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___115_1525 = x
in (

let uu____1526 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___115_1525.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_1525.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1526}))
in (((

let uu___116_1531 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.ty = uu___116_1531.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___116_1531.FStar_Syntax_Syntax.p})), ((n1 + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let x1 = (

let uu___117_1547 = x
in (

let uu____1548 = (subst' s1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___117_1547.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___117_1547.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1548}))
in (

let t01 = (subst' s1 t0)
in (((

let uu___118_1556 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.ty = uu___118_1556.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___118_1556.FStar_Syntax_Syntax.p})), (n1)))))
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

let uu___119_1594 = l
in (

let uu____1595 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___119_1594.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____1595; FStar_Syntax_Syntax.cflags = uu___119_1594.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____1598 -> (

let uu____1599 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s uu____1599)))}))
in FStar_Util.Inl (uu____1593))
in Some (uu____1590))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk1 = (fun t' -> (

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

let us1 = (FStar_List.map (subst_univ (Prims.fst s)) us)
in (

let uu____1675 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us1)
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
in (mk1 uu____1696))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t1) -> begin
(

let uu____1782 = (subst' s t1)
in FStar_Util.Inl (uu____1782))
end
| FStar_Util.Inr (c) -> begin
(

let uu____1796 = (subst_comp' s c)
in FStar_Util.Inr (uu____1796))
end)
in (

let uu____1803 = (

let uu____1804 = (

let uu____1822 = (subst' s t0)
in (

let uu____1825 = (

let uu____1837 = (FStar_Util.map_opt topt (subst' s))
in ((annot1), (uu____1837)))
in ((uu____1822), (uu____1825), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____1804))
in (mk1 uu____1803)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n1 = (FStar_List.length bs)
in (

let s' = (shift_subst' n1 s)
in (

let uu____1905 = (

let uu____1906 = (

let uu____1921 = (subst_binders' s bs)
in (

let uu____1925 = (subst' s' body)
in (

let uu____1928 = (push_subst_lcomp s' lopt)
in ((uu____1921), (uu____1925), (uu____1928)))))
in FStar_Syntax_Syntax.Tm_abs (uu____1906))
in (mk1 uu____1905))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n1 = (FStar_List.length bs)
in (

let uu____1965 = (

let uu____1966 = (

let uu____1974 = (subst_binders' s bs)
in (

let uu____1978 = (

let uu____1981 = (shift_subst' n1 s)
in (subst_comp' uu____1981 comp))
in ((uu____1974), (uu____1978))))
in FStar_Syntax_Syntax.Tm_arrow (uu____1966))
in (mk1 uu____1965)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x1 = (

let uu___120_2002 = x
in (

let uu____2003 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___120_2002.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___120_2002.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2003}))
in (

let phi1 = (

let uu____2009 = (shift_subst' (Prims.parse_int "1") s)
in (subst' uu____2009 phi))
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((x1), (phi1)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t01 = (subst' s t0)
in (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____2092 -> (match (uu____2092) with
| (pat, wopt, branch) -> begin
(

let uu____2128 = (subst_pat' s pat)
in (match (uu____2128) with
| (pat1, n1) -> begin
(

let s1 = (shift_subst' n1 s)
in (

let wopt1 = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____2163 = (subst' s1 w)
in Some (uu____2163))
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

let uu____2223 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____2223) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____2226 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___121_2233 = x
in {FStar_Syntax_Syntax.ppname = uu___121_2233.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___121_2233.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((

let uu___122_2235 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___123_2236 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___123_2236.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = uu___123_2236.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___122_2235.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___122_2235.FStar_Syntax_Syntax.fv_qual}))
end)
in (

let uu___124_2251 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___124_2251.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___124_2251.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (mk1 (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs1))), (body1)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let uu____2270 = (

let uu____2271 = (

let uu____2276 = (subst' s t0)
in (

let uu____2279 = (

let uu____2280 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____2280))
in ((uu____2276), (uu____2279))))
in FStar_Syntax_Syntax.Tm_meta (uu____2271))
in (mk1 uu____2270))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) -> begin
(

let uu____2322 = (

let uu____2323 = (

let uu____2328 = (subst' s t0)
in (

let uu____2331 = (

let uu____2332 = (

let uu____2337 = (subst' s t1)
in ((m), (uu____2337)))
in FStar_Syntax_Syntax.Meta_monadic (uu____2332))
in ((uu____2328), (uu____2331))))
in FStar_Syntax_Syntax.Tm_meta (uu____2323))
in (mk1 uu____2322))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) -> begin
(

let uu____2356 = (

let uu____2357 = (

let uu____2362 = (subst' s t0)
in (

let uu____2365 = (

let uu____2366 = (

let uu____2372 = (subst' s t1)
in ((m1), (m2), (uu____2372)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____2366))
in ((uu____2362), (uu____2365))))
in FStar_Syntax_Syntax.Tm_meta (uu____2357))
in (mk1 uu____2356))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____2385 = (

let uu____2386 = (

let uu____2391 = (subst' s t1)
in ((uu____2391), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____2386))
in (mk1 uu____2385))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (force_delayed_thunk t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t2, s), memo) -> begin
(

let t' = (

let uu____2454 = (push_subst s t2)
in (compress uu____2454))
in ((FStar_Unionfind.update_in_tx memo (Some (t')));
t';
))
end
| uu____2461 -> begin
(

let t' = (force_uvar t1)
in (match (t'.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2465) -> begin
(compress t')
end
| uu____2486 -> begin
t'
end))
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (subst' (([]), (Some ((

let uu___125_2510 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = uu___125_2510.FStar_Range.use_range})))) t))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (None)) t))


let closing_subst = (fun bs -> (

let uu____2538 = (FStar_List.fold_right (fun uu____2547 uu____2548 -> (match (((uu____2547), (uu____2548))) with
| ((x, uu____2563), (subst1, n1)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n1))))::subst1), ((n1 + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right uu____2538 Prims.fst)))


let open_binders' = (fun bs -> (

let rec aux = (fun bs1 o -> (match (bs1) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___126_2643 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____2644 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___126_2643.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___126_2643.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2644}))
in (

let o1 = (

let uu____2649 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____2649)
in (

let uu____2651 = (aux bs' o1)
in (match (uu____2651) with
| (bs'1, o2) -> begin
(((((x'), (imp)))::bs'1), (o2))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____2683 = (open_binders' bs)
in (Prims.fst uu____2683)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____2703 = (open_binders' bs)
in (match (uu____2703) with
| (bs', opening) -> begin
(

let uu____2723 = (subst opening t)
in ((bs'), (uu____2723), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____2736 = (open_term' bs t)
in (match (uu____2736) with
| (b, t1, uu____2744) -> begin
((b), (t1))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____2753 = (open_binders' bs)
in (match (uu____2753) with
| (bs', opening) -> begin
(

let uu____2772 = (subst_comp opening t)
in ((bs'), (uu____2772)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec aux_disj = (fun sub1 renaming p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____2809) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (uu____2815) -> begin
p1
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu___127_2828 = p1
in (

let uu____2831 = (

let uu____2832 = (

let uu____2840 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____2864 -> (match (uu____2864) with
| (p2, b) -> begin
(

let uu____2879 = (aux_disj sub1 renaming p2)
in ((uu____2879), (b)))
end))))
in ((fv), (uu____2840)))
in FStar_Syntax_Syntax.Pat_cons (uu____2832))
in {FStar_Syntax_Syntax.v = uu____2831; FStar_Syntax_Syntax.ty = uu___127_2828.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___127_2828.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let yopt = (FStar_Util.find_map renaming (fun uu___104_2894 -> (match (uu___104_2894) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| uu____2900 -> begin
None
end)))
in (

let y = (match (yopt) with
| None -> begin
(

let uu___128_2904 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____2905 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___128_2904.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___128_2904.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2905}))
end
| Some (y) -> begin
y
end)
in (

let uu___129_2909 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = uu___129_2909.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___129_2909.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___130_2914 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____2915 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___130_2914.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___130_2914.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2915}))
in (

let uu___131_2918 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = uu___131_2918.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___131_2918.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___132_2928 = x
in (

let uu____2929 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___132_2928.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___132_2928.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2929}))
in (

let t01 = (subst sub1 t0)
in (

let uu___133_2933 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.ty = uu___133_2933.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___133_2933.FStar_Syntax_Syntax.p})))
end))
in (

let rec aux = (fun sub1 renaming p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (uu____2987) -> begin
((p1), (sub1), (renaming))
end
| FStar_Syntax_Syntax.Pat_disj ((p2)::ps) -> begin
(

let uu____3003 = (aux sub1 renaming p2)
in (match (uu____3003) with
| (p3, sub2, renaming1) -> begin
(

let ps1 = (FStar_List.map (aux_disj sub2 renaming1) ps)
in (((

let uu___134_3051 = p3
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p3)::ps1); FStar_Syntax_Syntax.ty = uu___134_3051.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___134_3051.FStar_Syntax_Syntax.p})), (sub2), (renaming1)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3068 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____3114 uu____3115 -> (match (((uu____3114), (uu____3115))) with
| ((pats1, sub2, renaming1), (p2, imp)) -> begin
(

let uu____3203 = (aux sub2 renaming1 p2)
in (match (uu____3203) with
| (p3, sub3, renaming2) -> begin
(((((p3), (imp)))::pats1), (sub3), (renaming2))
end))
end)) (([]), (sub1), (renaming))))
in (match (uu____3068) with
| (pats1, sub2, renaming1) -> begin
(((

let uu___135_3304 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.ty = uu___135_3304.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___135_3304.FStar_Syntax_Syntax.p})), (sub2), (renaming1))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___136_3318 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____3319 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___136_3318.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___136_3318.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3319}))
in (

let sub2 = (

let uu____3324 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____3324)
in (((

let uu___137_3332 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = uu___137_3332.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___137_3332.FStar_Syntax_Syntax.p})), (sub2), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___138_3339 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let uu____3340 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___138_3339.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___138_3339.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3340}))
in (

let sub2 = (

let uu____3345 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::uu____3345)
in (((

let uu___139_3353 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = uu___139_3353.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___139_3353.FStar_Syntax_Syntax.p})), (sub2), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___140_3365 = x
in (

let uu____3366 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___140_3365.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___140_3365.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3366}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___141_3376 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.ty = uu___141_3376.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___141_3376.FStar_Syntax_Syntax.p})), (sub1), (renaming))))
end))
in (

let uu____3379 = (aux [] [] p)
in (match (uu____3379) with
| (p1, sub1, uu____3395) -> begin
((p1), (sub1))
end)))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____3413 -> (match (uu____3413) with
| (p, wopt, e) -> begin
(

let uu____3431 = (open_pat p)
in (match (uu____3431) with
| (p1, opening) -> begin
(

let wopt1 = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____3446 = (subst opening w)
in Some (uu____3446))
end)
in (

let e1 = (subst opening e)
in ((p1), (wopt1), (e1))))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (

let uu____3455 = (closing_subst bs)
in (subst uu____3455 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (

let uu____3463 = (closing_subst bs)
in (subst_comp uu____3463 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs1 -> (match (bs1) with
| [] -> begin
[]
end
| ((x, imp))::tl1 -> begin
(

let x1 = (

let uu___142_3496 = x
in (

let uu____3497 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___142_3496.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___142_3496.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3497}))
in (

let s' = (

let uu____3502 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____3502)
in (

let uu____3504 = (aux s' tl1)
in (((x1), (imp)))::uu____3504)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let uu___143_3518 = lc
in (

let uu____3519 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___143_3518.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____3519; FStar_Syntax_Syntax.cflags = uu___143_3518.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____3522 -> (

let uu____3523 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s uu____3523)))}))))


let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (uu____3566) -> begin
((p1), (sub1))
end
| FStar_Syntax_Syntax.Pat_disj ((p2)::ps) -> begin
(

let uu____3579 = (aux sub1 p2)
in (match (uu____3579) with
| (p3, sub2) -> begin
(

let ps1 = (FStar_List.map (fun p4 -> (

let uu____3609 = (aux sub2 p4)
in (Prims.fst uu____3609))) ps)
in (((

let uu___144_3621 = p3
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p3)::ps1); FStar_Syntax_Syntax.ty = uu___144_3621.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___144_3621.FStar_Syntax_Syntax.p})), (sub2)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3638 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____3672 uu____3673 -> (match (((uu____3672), (uu____3673))) with
| ((pats1, sub2), (p2, imp)) -> begin
(

let uu____3738 = (aux sub2 p2)
in (match (uu____3738) with
| (p3, sub3) -> begin
(((((p3), (imp)))::pats1), (sub3))
end))
end)) (([]), (sub1))))
in (match (uu____3638) with
| (pats1, sub2) -> begin
(((

let uu___145_3804 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.ty = uu___145_3804.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___145_3804.FStar_Syntax_Syntax.p})), (sub2))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___146_3818 = x
in (

let uu____3819 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___146_3818.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___146_3818.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3819}))
in (

let sub2 = (

let uu____3824 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____3824)
in (((

let uu___147_3829 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.ty = uu___147_3829.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___147_3829.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___148_3834 = x
in (

let uu____3835 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___148_3834.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___148_3834.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3835}))
in (

let sub2 = (

let uu____3840 = (shift_subst (Prims.parse_int "1") sub1)
in (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::uu____3840)
in (((

let uu___149_3845 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.ty = uu___149_3845.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___149_3845.FStar_Syntax_Syntax.p})), (sub2))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x1 = (

let uu___150_3855 = x
in (

let uu____3856 = (subst sub1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___150_3855.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_3855.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3856}))
in (

let t01 = (subst sub1 t0)
in (((

let uu___151_3863 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t01))); FStar_Syntax_Syntax.ty = uu___151_3863.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___151_3863.FStar_Syntax_Syntax.p})), (sub1))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____3868 -> (match (uu____3868) with
| (p, wopt, e) -> begin
(

let uu____3886 = (close_pat p)
in (match (uu____3886) with
| (p1, closing) -> begin
(

let wopt1 = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____3910 = (subst closing w)
in Some (uu____3910))
end)
in (

let e1 = (subst closing e)
in ((p1), (wopt1), (e1))))
end))
end))


let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let uu____3926 = (

let uu____3931 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (

let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in ((FStar_Syntax_Syntax.UN ((((n1 - i)), (FStar_Syntax_Syntax.U_name (u'))))), (u'))))))
in (FStar_All.pipe_right uu____3931 FStar_List.unzip))
in (match (uu____3926) with
| (s, us') -> begin
((s), (us'))
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (

let uu____3972 = (univ_var_opening us)
in (match (uu____3972) with
| (s, us') -> begin
(

let t1 = (subst s t)
in ((us'), (t1)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____3997 = (univ_var_opening us)
in (match (uu____3997) with
| (s, us') -> begin
(

let uu____4010 = (subst_comp s c)
in ((us'), (uu____4010)))
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

let uu____4053 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____4053) with
| true -> begin
((lbs), (t))
end
| uu____4058 -> begin
(

let uu____4059 = (FStar_List.fold_right (fun lb uu____4071 -> (match (uu____4071) with
| (i, lbs1, out) -> begin
(

let x = (

let uu____4090 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____4090))
in (((i + (Prims.parse_int "1"))), (((

let uu___152_4093 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___152_4093.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___152_4093.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___152_4093.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___152_4093.FStar_Syntax_Syntax.lbdef}))::lbs1), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
in (match (uu____4059) with
| (n_let_recs, lbs1, let_rec_opening) -> begin
(

let lbs2 = (FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let uu____4111 = (FStar_List.fold_right (fun u uu____4123 -> (match (uu____4123) with
| (i, us, out) -> begin
(

let u1 = (FStar_Syntax_Syntax.new_univ_name None)
in (((i + (Prims.parse_int "1"))), ((u1)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u1)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____4111) with
| (uu____4146, us, u_let_rec_opening) -> begin
(

let uu___153_4153 = lb
in (

let uu____4154 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___153_4153.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu___153_4153.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___153_4153.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____4154}))
end)))))
in (

let t1 = (subst let_rec_opening t)
in ((lbs2), (t1))))
end))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____4170 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____4170) with
| true -> begin
((lbs), (t))
end
| uu____4175 -> begin
(

let uu____4176 = (FStar_List.fold_right (fun lb uu____4184 -> (match (uu____4184) with
| (i, out) -> begin
(

let uu____4195 = (

let uu____4197 = (

let uu____4198 = (

let uu____4201 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____4201), (i)))
in FStar_Syntax_Syntax.NM (uu____4198))
in (uu____4197)::out)
in (((i + (Prims.parse_int "1"))), (uu____4195)))
end)) lbs (((Prims.parse_int "0")), ([])))
in (match (uu____4176) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____4216 = (FStar_List.fold_right (fun u uu____4224 -> (match (uu____4224) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____4216) with
| (uu____4237, u_let_rec_closing) -> begin
(

let uu___154_4241 = lb
in (

let uu____4242 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___154_4241.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___154_4241.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___154_4241.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___154_4241.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____4242}))
end)))))
in (

let t1 = (subst let_rec_closing t)
in ((lbs1), (t1))))
end))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____4252 -> (match (uu____4252) with
| (us, t) -> begin
(

let n1 = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____4270 -> (match (uu____4270) with
| (x, uu____4274) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n1 - i)))))
end)) binders)
in (

let t1 = (subst s t)
in ((us), (t1))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____4285 -> (match (uu____4285) with
| (us', t) -> begin
(

let n1 = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n1 - i)))))) us)
in (

let uu____4303 = (subst s t)
in ((us'), (uu____4303))))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n1 = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____4318 -> (match (uu____4318) with
| (x, uu____4322) -> begin
FStar_Syntax_Syntax.DB ((((n1 - i)), (x)))
end))))))




