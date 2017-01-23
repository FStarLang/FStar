
open Prims

let subst_to_string = (fun s -> (let _0_52 = (FStar_All.pipe_right s (FStar_List.map (fun uu____21 -> (match (uu____21) with
| (b, uu____25) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _0_52 (FStar_String.concat ", "))))


let rec apply_until_some = (fun f s -> (match (s) with
| [] -> begin
None
end
| (s0)::rest -> begin
(

let uu____59 = (f s0)
in (match (uu____59) with
| None -> begin
(apply_until_some f rest)
end
| Some (st) -> begin
Some (((rest), (st)))
end))
end))


let map_some_curry = (fun f x uu___100_99 -> (match (uu___100_99) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map = (fun f s g t -> (let _0_53 = (apply_until_some f s)
in (FStar_All.pipe_right _0_53 (map_some_curry g t))))


let compose_subst = (fun s1 s2 -> (

let s = (FStar_List.append (Prims.fst s1) (Prims.fst s2))
in (

let ropt = (match ((Prims.snd s2)) with
| Some (uu____210) -> begin
(Prims.snd s2)
end
| uu____213 -> begin
(Prims.snd s1)
end)
in ((s), (ropt)))))


let delay : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  FStar_Syntax_Syntax.term = (fun t s -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t'), ((compose_subst s' s))))) t.FStar_Syntax_Syntax.pos)
end
| uu____309 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t), (s)))) t.FStar_Syntax_Syntax.pos)
end))


let rec force_uvar' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____340) -> begin
(

let uu____353 = (FStar_Unionfind.find uv)
in (match (uu____353) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar' t')
end
| uu____367 -> begin
t
end))
end
| uu____371 -> begin
t
end))


let force_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (

let t' = (force_uvar' t)
in (

let uu____384 = (FStar_Util.physical_equality t t')
in (match (uu____384) with
| true -> begin
t
end
| uu____389 -> begin
(delay t' (([]), (Some (t.FStar_Syntax_Syntax.pos))))
end))))


let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(

let uu____443 = (FStar_ST.read m)
in (match (uu____443) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(

let t' = (force_delayed_thunk (c ()))
in ((FStar_ST.write m (Some (t')));
t';
))
end
| uu____487 -> begin
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
| uu____519 -> begin
t
end))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(

let uu____526 = (FStar_Unionfind.find u')
in (match (uu____526) with
| Some (u) -> begin
(compress_univ u)
end
| uu____530 -> begin
u
end))
end
| uu____532 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun uu___101_542 -> (match (uu___101_542) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
Some ((FStar_Syntax_Syntax.bv_to_name (let _0_54 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x _0_54))))
end
| uu____546 -> begin
None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun uu___102_556 -> (match (uu___102_556) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some ((FStar_Syntax_Syntax.bv_to_tm (

let uu___107_560 = a
in {FStar_Syntax_Syntax.ppname = uu___107_560.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___107_560.FStar_Syntax_Syntax.sort})))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| uu____569 -> begin
None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun uu___103_579 -> (match (uu___103_579) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| uu____583 -> begin
None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun uu___104_593 -> (match (uu___104_593) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| uu____597 -> begin
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
FStar_Syntax_Syntax.U_succ ((subst_univ s u))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
FStar_Syntax_Syntax.U_max ((FStar_List.map (subst_univ s) us))
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
FStar_Syntax_Syntax.Tm_bvar ((FStar_Syntax_Syntax.set_range_of_bv bv r))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
FStar_Syntax_Syntax.Tm_name ((FStar_Syntax_Syntax.set_range_of_bv bv r))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v = (

let uu___108_656 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r); FStar_Syntax_Syntax.ty = uu___108_656.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___108_656.FStar_Syntax_Syntax.p})
in (

let fv = (

let uu___109_672 = fv
in {FStar_Syntax_Syntax.fv_name = v; FStar_Syntax_Syntax.fv_delta = uu___109_672.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___109_672.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv))))
end
| t' -> begin
t'
end)
in (

let uu___110_674 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.tk = uu___110_674.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___110_674.FStar_Syntax_Syntax.vars})))
end))


let tag_lid_with_range = (fun l s -> (match ((Prims.snd s)) with
| None -> begin
l
end
| Some (r) -> begin
(let _0_55 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r)
in (FStar_Ident.set_lid_range l _0_55))
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
| uu____782 -> begin
(

let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t'), ((compose_subst s' s))))) t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (uu____863), uu____864) -> begin
(failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) (Prims.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) (Prims.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _0_56 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type ((subst_univ (Prims.fst s) u)))) None _0_56))
end
| uu____931 -> begin
(let _0_57 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t0), (s)))) _0_57))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___105_945 -> (match (uu___105_945) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
FStar_Syntax_Syntax.DECREASES ((subst' s a))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| (([], None)) | ((([])::[], None)) -> begin
t
end
| uu____966 -> begin
(

let uu___111_972 = t
in (let _0_63 = (FStar_List.map (subst_univ (Prims.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (let _0_62 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (let _0_61 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _0_60 = (FStar_List.map (fun uu____986 -> (match (uu____986) with
| (t, imp) -> begin
(let _0_58 = (subst' s t)
in ((_0_58), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _0_59 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = _0_63; FStar_Syntax_Syntax.effect_name = _0_62; FStar_Syntax_Syntax.result_typ = _0_61; FStar_Syntax_Syntax.effect_args = _0_60; FStar_Syntax_Syntax.flags = _0_59}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| (([], None)) | ((([])::[], None)) -> begin
t
end
| uu____1023 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _0_65 = (subst' s t)
in (let _0_64 = (FStar_Option.map (subst_univ (Prims.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' _0_65 _0_64)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _0_67 = (subst' s t)
in (let _0_66 = (FStar_Option.map (subst_univ (Prims.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _0_67 _0_66)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (subst_comp_typ' s ct))
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
| FStar_Syntax_Syntax.NT (uu____1068) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))


let shift_subst' = (fun n s -> (let _0_68 = (FStar_All.pipe_right (Prims.fst s) (FStar_List.map (shift_subst n)))
in ((_0_68), ((Prims.snd s)))))


let subst_binder' = (fun s uu____1120 -> (match (uu____1120) with
| (x, imp) -> begin
(let _0_70 = (

let uu___112_1125 = x
in (let _0_69 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___112_1125.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___112_1125.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_69}))
in ((_0_70), (imp)))
end))


let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> (match ((i = (Prims.parse_int "0"))) with
| true -> begin
(subst_binder' s b)
end
| uu____1163 -> begin
(let _0_71 = (shift_subst' i s)
in (subst_binder' _0_71 b))
end)))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (None)) bs))


let subst_arg' = (fun s uu____1197 -> (match (uu____1197) with
| (t, imp) -> begin
(let _0_72 = (subst' s t)
in ((_0_72), (imp)))
end))


let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range Prims.option)  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (uu____1280) -> begin
((p), (n))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let uu____1292 = (aux n p)
in (match (uu____1292) with
| (p, m) -> begin
(

let ps = (FStar_List.map (fun p -> (Prims.fst (aux n p))) ps)
in (((

let uu___113_1308 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = uu___113_1308.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___113_1308.FStar_Syntax_Syntax.p})), (m)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1321 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1346 uu____1347 -> (match (((uu____1346), (uu____1347))) with
| ((pats, n), (p, imp)) -> begin
(

let uu____1394 = (aux n p)
in (match (uu____1394) with
| (p, m) -> begin
(((((p), (imp)))::pats), (m))
end))
end)) (([]), (n))))
in (match (uu____1321) with
| (pats, n) -> begin
(((

let uu___114_1426 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = uu___114_1426.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___114_1426.FStar_Syntax_Syntax.p})), (n))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let uu___115_1442 = x
in (let _0_73 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___115_1442.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_1442.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_73}))
in (((

let uu___116_1445 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = uu___116_1445.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___116_1445.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let uu___117_1456 = x
in (let _0_74 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___117_1456.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___117_1456.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_74}))
in (((

let uu___118_1459 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = uu___118_1459.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___118_1459.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let uu___119_1475 = x
in (let _0_75 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___119_1475.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___119_1475.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_75}))
in (

let t0 = (subst' s t0)
in (((

let uu___120_1481 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = uu___120_1481.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___120_1481.FStar_Syntax_Syntax.p})), (n)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (l)) -> begin
Some (FStar_Util.Inl ((

let uu___121_1517 = l
in (let _0_77 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___121_1517.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _0_77; FStar_Syntax_Syntax.cflags = uu___121_1517.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____1518 -> (let _0_76 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _0_76)))}))))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk = (fun t' -> (let _0_78 = (mk_range t.FStar_Syntax_Syntax.pos s)
in ((FStar_Syntax_Syntax.mk t') None _0_78)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1547) -> begin
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
in (let _0_79 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us)
in (tag_with_range _0_79 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((let _0_81 = (subst' s t0)
in (let _0_80 = ((subst_args' s) args)
in ((_0_81), (_0_80)))))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inl (t1), lopt) -> begin
(mk (FStar_Syntax_Syntax.Tm_ascribed ((let _0_83 = (subst' s t0)
in (let _0_82 = FStar_Util.Inl ((subst' s t1))
in ((_0_83), (_0_82), (lopt)))))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inr (c), lopt) -> begin
(mk (FStar_Syntax_Syntax.Tm_ascribed ((let _0_85 = (subst' s t0)
in (let _0_84 = FStar_Util.Inr ((subst_comp' s c))
in ((_0_85), (_0_84), (lopt)))))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n = (FStar_List.length bs)
in (

let s' = (shift_subst' n s)
in (mk (FStar_Syntax_Syntax.Tm_abs ((let _0_88 = (subst_binders' s bs)
in (let _0_87 = (subst' s' body)
in (let _0_86 = (push_subst_lcomp s' lopt)
in ((_0_88), (_0_87), (_0_86))))))))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n = (FStar_List.length bs)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((let _0_91 = (subst_binders' s bs)
in (let _0_90 = (let _0_89 = (shift_subst' n s)
in (subst_comp' _0_89 comp))
in ((_0_91), (_0_90))))))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x = (

let uu___122_1764 = x
in (let _0_92 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___122_1764.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___122_1764.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_92}))
in (

let phi = (let _0_93 = (shift_subst' (Prims.parse_int "1") s)
in (subst' _0_93 phi))
in (mk (FStar_Syntax_Syntax.Tm_refine (((x), (phi)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t0 = (subst' s t0)
in (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun uu____1850 -> (match (uu____1850) with
| (pat, wopt, branch) -> begin
(

let uu____1886 = (subst_pat' s pat)
in (match (uu____1886) with
| (pat, n) -> begin
(

let s = (shift_subst' n s)
in (

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
Some ((subst' s w))
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

let uu____1978 = (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname))
in (match (uu____1978) with
| true -> begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end
| uu____1981 -> begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let uu___123_1988 = x
in {FStar_Syntax_Syntax.ppname = uu___123_1988.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_1988.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((

let uu___124_1990 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___125_1991 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___125_1991.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = uu___125_1991.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___124_1990.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___124_1990.FStar_Syntax_Syntax.fv_qual}))
end)
in (

let uu___126_2006 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___126_2006.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = uu___126_2006.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (mk (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs))), (body)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((let _0_95 = (subst' s t0)
in (let _0_94 = FStar_Syntax_Syntax.Meta_pattern ((FStar_All.pipe_right ps (FStar_List.map (subst_args' s))))
in ((_0_95), (_0_94)))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t)) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((let _0_98 = (subst' s t0)
in (let _0_97 = FStar_Syntax_Syntax.Meta_monadic ((let _0_96 = (subst' s t)
in ((m), (_0_96))))
in ((_0_98), (_0_97)))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t)) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((let _0_101 = (subst' s t0)
in (let _0_100 = FStar_Syntax_Syntax.Meta_monadic_lift ((let _0_99 = (subst' s t)
in ((m1), (m2), (_0_99))))
in ((_0_101), (_0_100)))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((let _0_102 = (subst' s t)
in ((_0_102), (m))))))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(

let t' = (compress (push_subst s t))
in ((FStar_Unionfind.update_in_tx memo (Some (t')));
t';
))
end
| uu____2152 -> begin
(

let t' = (force_uvar t)
in (match (t'.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2156) -> begin
(compress t')
end
| uu____2177 -> begin
t'
end))
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (subst' (([]), (Some ((

let uu___127_2201 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = uu___127_2201.FStar_Range.use_range})))) t))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (None)) t))


let closing_subst = (fun bs -> (let _0_103 = (FStar_List.fold_right (fun uu____2238 uu____2239 -> (match (((uu____2238), (uu____2239))) with
| ((x, uu____2254), (subst, n)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n))))::subst), ((n + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right _0_103 Prims.fst)))


let open_binders' = (fun bs -> (

let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let uu___128_2330 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _0_104 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___128_2330.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___128_2330.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_104}))
in (

let o = (let _0_105 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_0_105)
in (

let uu____2333 = (aux bs' o)
in (match (uu____2333) with
| (bs', o) -> begin
(((((x'), (imp)))::bs'), (o))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (Prims.fst (open_binders' bs)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let uu____2378 = (open_binders' bs)
in (match (uu____2378) with
| (bs', opening) -> begin
(let _0_106 = (subst opening t)
in ((bs'), (_0_106), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let uu____2410 = (open_term' bs t)
in (match (uu____2410) with
| (b, t, uu____2418) -> begin
((b), (t))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let uu____2427 = (open_binders' bs)
in (match (uu____2427) with
| (bs', opening) -> begin
(let _0_107 = (subst_comp opening t)
in ((bs'), (_0_107)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec aux_disj = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____2482) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (uu____2488) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu___129_2501 = p
in (let _0_110 = FStar_Syntax_Syntax.Pat_cons ((let _0_109 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____2527 -> (match (uu____2527) with
| (p, b) -> begin
(let _0_108 = (aux_disj sub renaming p)
in ((_0_108), (b)))
end))))
in ((fv), (_0_109))))
in {FStar_Syntax_Syntax.v = _0_110; FStar_Syntax_Syntax.ty = uu___129_2501.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___129_2501.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let yopt = (FStar_Util.find_map renaming (fun uu___106_2549 -> (match (uu___106_2549) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| uu____2555 -> begin
None
end)))
in (

let y = (match (yopt) with
| None -> begin
(

let uu___130_2559 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _0_111 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___130_2559.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___130_2559.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_111}))
end
| Some (y) -> begin
y
end)
in (

let uu___131_2561 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = uu___131_2561.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___131_2561.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___132_2566 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _0_112 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___132_2566.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___132_2566.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_112}))
in (

let uu___133_2567 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = uu___133_2567.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___133_2567.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let uu___134_2577 = x
in (let _0_113 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___134_2577.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___134_2577.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_113}))
in (

let t0 = (subst sub t0)
in (

let uu___135_2579 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = uu___135_2579.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___135_2579.FStar_Syntax_Syntax.p})))
end))
in (

let rec aux = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (uu____2633) -> begin
((p), (sub), (renaming))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let uu____2649 = (aux sub renaming p)
in (match (uu____2649) with
| (p, sub, renaming) -> begin
(

let ps = (FStar_List.map (aux_disj sub renaming) ps)
in (((

let uu___136_2697 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = uu___136_2697.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___136_2697.FStar_Syntax_Syntax.p})), (sub), (renaming)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2714 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____2760 uu____2761 -> (match (((uu____2760), (uu____2761))) with
| ((pats, sub, renaming), (p, imp)) -> begin
(

let uu____2849 = (aux sub renaming p)
in (match (uu____2849) with
| (p, sub, renaming) -> begin
(((((p), (imp)))::pats), (sub), (renaming))
end))
end)) (([]), (sub), (renaming))))
in (match (uu____2714) with
| (pats, sub, renaming) -> begin
(((

let uu___137_2950 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = uu___137_2950.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___137_2950.FStar_Syntax_Syntax.p})), (sub), (renaming))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let uu___138_2964 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _0_114 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___138_2964.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___138_2964.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_114}))
in (

let sub = (let _0_115 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_0_115)
in (((

let uu___139_2973 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = uu___139_2973.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___139_2973.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let uu___140_2980 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _0_116 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___140_2980.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___140_2980.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_116}))
in (

let sub = (let _0_117 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_0_117)
in (((

let uu___141_2989 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = uu___141_2989.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___141_2989.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let uu___142_3001 = x
in (let _0_118 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___142_3001.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___142_3001.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_118}))
in (

let t0 = (subst sub t0)
in (((

let uu___143_3009 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = uu___143_3009.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___143_3009.FStar_Syntax_Syntax.p})), (sub), (renaming))))
end))
in (

let uu____3012 = (aux [] [] p)
in (match (uu____3012) with
| (p, sub, uu____3028) -> begin
((p), (sub))
end)))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____3046 -> (match (uu____3046) with
| (p, wopt, e) -> begin
(

let uu____3064 = (open_pat p)
in (match (uu____3064) with
| (p, opening) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
Some ((subst opening w))
end)
in (

let e = (subst opening e)
in ((p), (wopt), (e))))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _0_119 = (closing_subst bs)
in (subst _0_119 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _0_120 = (closing_subst bs)
in (subst_comp _0_120 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| ((x, imp))::tl -> begin
(

let x = (

let uu___144_3124 = x
in (let _0_121 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___144_3124.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___144_3124.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_121}))
in (

let s' = (let _0_122 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_0_122)
in (let _0_123 = (aux s' tl)
in (((x), (imp)))::_0_123)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let uu___145_3137 = lc
in (let _0_125 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___145_3137.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _0_125; FStar_Syntax_Syntax.cflags = uu___145_3137.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____3138 -> (let _0_124 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _0_124)))}))))


let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (uu____3181) -> begin
((p), (sub))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let uu____3194 = (aux sub p)
in (match (uu____3194) with
| (p, sub) -> begin
(

let ps = (FStar_List.map (fun p -> (Prims.fst (aux sub p))) ps)
in (((

let uu___146_3230 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = uu___146_3230.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___146_3230.FStar_Syntax_Syntax.p})), (sub)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3247 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____3281 uu____3282 -> (match (((uu____3281), (uu____3282))) with
| ((pats, sub), (p, imp)) -> begin
(

let uu____3347 = (aux sub p)
in (match (uu____3347) with
| (p, sub) -> begin
(((((p), (imp)))::pats), (sub))
end))
end)) (([]), (sub))))
in (match (uu____3247) with
| (pats, sub) -> begin
(((

let uu___147_3413 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = uu___147_3413.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___147_3413.FStar_Syntax_Syntax.p})), (sub))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let uu___148_3427 = x
in (let _0_126 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___148_3427.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___148_3427.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_126}))
in (

let sub = (let _0_127 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_0_127)
in (((

let uu___149_3433 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = uu___149_3433.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___149_3433.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let uu___150_3438 = x
in (let _0_128 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___150_3438.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_3438.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_128}))
in (

let sub = (let _0_129 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_0_129)
in (((

let uu___151_3444 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = uu___151_3444.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___151_3444.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let uu___152_3454 = x
in (let _0_130 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___152_3454.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___152_3454.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_130}))
in (

let t0 = (subst sub t0)
in (((

let uu___153_3459 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = uu___153_3459.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___153_3459.FStar_Syntax_Syntax.p})), (sub))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun uu____3464 -> (match (uu____3464) with
| (p, wopt, e) -> begin
(

let uu____3482 = (close_pat p)
in (match (uu____3482) with
| (p, closing) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
Some ((subst closing w))
end)
in (

let e = (subst closing e)
in ((p), (wopt), (e))))
end))
end))


let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let uu____3521 = (let _0_131 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (

let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in ((FStar_Syntax_Syntax.UN ((((n - i)), (FStar_Syntax_Syntax.U_name (u'))))), (u'))))))
in (FStar_All.pipe_right _0_131 FStar_List.unzip))
in (match (uu____3521) with
| (s, us') -> begin
((s), (us'))
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (

let uu____3563 = (univ_var_opening us)
in (match (uu____3563) with
| (s, us') -> begin
(

let t = (subst s t)
in ((us'), (t)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let uu____3588 = (univ_var_opening us)
in (match (uu____3588) with
| (s, us') -> begin
(let _0_132 = (subst_comp s c)
in ((us'), (_0_132)))
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

let uu____3643 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____3643) with
| true -> begin
((lbs), (t))
end
| uu____3648 -> begin
(

let uu____3649 = (FStar_List.fold_right (fun lb uu____3661 -> (match (uu____3661) with
| (i, lbs, out) -> begin
(

let x = (FStar_Syntax_Syntax.freshen_bv (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))
in (((i + (Prims.parse_int "1"))), (((

let uu___154_3682 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___154_3682.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___154_3682.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___154_3682.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___154_3682.FStar_Syntax_Syntax.lbdef}))::lbs), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
in (match (uu____3649) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____3700 = (FStar_List.fold_right (fun u uu____3712 -> (match (uu____3712) with
| (i, us, out) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name None)
in (((i + (Prims.parse_int "1"))), ((u)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (uu____3700) with
| (uu____3735, us, u_let_rec_opening) -> begin
(

let uu___155_3742 = lb
in (let _0_133 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___155_3742.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = uu___155_3742.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___155_3742.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _0_133}))
end)))))
in (

let t = (subst let_rec_opening t)
in ((lbs), (t))))
end))
end)))


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> (

let uu____3756 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____3756) with
| true -> begin
((lbs), (t))
end
| uu____3761 -> begin
(

let uu____3762 = (FStar_List.fold_right (fun lb uu____3770 -> (match (uu____3770) with
| (i, out) -> begin
(let _0_136 = (let _0_135 = FStar_Syntax_Syntax.NM ((let _0_134 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((_0_134), (i))))
in (_0_135)::out)
in (((i + (Prims.parse_int "1"))), (_0_136)))
end)) lbs (((Prims.parse_int "0")), ([])))
in (match (uu____3762) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____3795 = (FStar_List.fold_right (fun u uu____3803 -> (match (uu____3803) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (uu____3795) with
| (uu____3816, u_let_rec_closing) -> begin
(

let uu___156_3820 = lb
in (let _0_137 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___156_3820.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___156_3820.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___156_3820.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___156_3820.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _0_137}))
end)))))
in (

let t = (subst let_rec_closing t)
in ((lbs), (t))))
end))
end)))


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders uu____3828 -> (match (uu____3828) with
| (us, t) -> begin
(

let n = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i uu____3846 -> (match (uu____3846) with
| (x, uu____3850) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n - i)))))
end)) binders)
in (

let t = (subst s t)
in ((us), (t))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us uu____3861 -> (match (uu____3861) with
| (us', t) -> begin
(

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n - i)))))) us)
in (let _0_138 = (subst s t)
in ((us'), (_0_138))))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i uu____3893 -> (match (uu____3893) with
| (x, uu____3897) -> begin
FStar_Syntax_Syntax.DB ((((n - i)), (x)))
end))))))




