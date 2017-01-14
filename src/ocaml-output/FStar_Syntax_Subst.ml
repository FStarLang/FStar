
open Prims

let subst_to_string = (fun s -> (let _138_3 = (FStar_All.pipe_right s (FStar_List.map (fun _37_5 -> (match (_37_5) with
| (b, _37_4) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _138_3 (FStar_String.concat ", "))))


let rec apply_until_some = (fun f s -> (match (s) with
| [] -> begin
None
end
| (s0)::rest -> begin
(match ((f s0)) with
| None -> begin
(apply_until_some f rest)
end
| Some (st) -> begin
Some (((rest), (st)))
end)
end))


let map_some_curry = (fun f x uu___67 -> (match (uu___67) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map = (fun f s g t -> (let _138_31 = (apply_until_some f s)
in (FStar_All.pipe_right _138_31 (map_some_curry g t))))


let compose_subst = (fun s1 s2 -> (

let s = (FStar_List.append (Prims.fst s1) (Prims.fst s2))
in (

let ropt = (match ((Prims.snd s2)) with
| Some (_37_31) -> begin
(Prims.snd s2)
end
| _37_34 -> begin
(Prims.snd s1)
end)
in ((s), (ropt)))))


let delay : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  FStar_Syntax_Syntax.term = (fun t s -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t'), ((compose_subst s' s))))) t.FStar_Syntax_Syntax.pos)
end
| _37_46 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t), (s)))) t.FStar_Syntax_Syntax.pos)
end))


let rec force_uvar' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _37_50) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar' t')
end
| _37_56 -> begin
t
end)
end
| _37_58 -> begin
t
end))


let force_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (

let t' = (force_uvar' t)
in if (FStar_Util.physical_equality t t') then begin
t
end else begin
(delay t' (([]), (Some (t.FStar_Syntax_Syntax.pos))))
end))


let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(

let t' = (let _138_49 = (c ())
in (force_delayed_thunk _138_49))
in (

let _37_70 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _37_73 -> begin
t
end)
end
| Some (t') -> begin
(

let t' = (force_delayed_thunk t')
in (

let _37_77 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _37_80 -> begin
t
end))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(match ((FStar_Unionfind.find u')) with
| Some (u) -> begin
(compress_univ u)
end
| _37_87 -> begin
u
end)
end
| _37_89 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun uu___68 -> (match (uu___68) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(let _138_61 = (let _138_60 = (let _138_59 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x _138_59))
in (FStar_Syntax_Syntax.bv_to_name _138_60))
in Some (_138_61))
end
| _37_98 -> begin
None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun uu___69 -> (match (uu___69) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _138_67 = (FStar_Syntax_Syntax.bv_to_tm (

let _37_106 = a
in {FStar_Syntax_Syntax.ppname = _37_106.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _37_106.FStar_Syntax_Syntax.sort}))
in Some (_138_67))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _37_113 -> begin
None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun uu___70 -> (match (uu___70) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _37_122 -> begin
None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun uu___71 -> (match (uu___71) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _37_131 -> begin
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
(let _138_82 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_138_82))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _138_83 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_138_83))
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
(let _138_86 = (FStar_Syntax_Syntax.set_range_of_bv bv r)
in FStar_Syntax_Syntax.Tm_bvar (_138_86))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(let _138_87 = (FStar_Syntax_Syntax.set_range_of_bv bv r)
in FStar_Syntax_Syntax.Tm_name (_138_87))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v = (

let _37_161 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r); FStar_Syntax_Syntax.ty = _37_161.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_161.FStar_Syntax_Syntax.p})
in (

let fv = (

let _37_164 = fv
in {FStar_Syntax_Syntax.fv_name = v; FStar_Syntax_Syntax.fv_delta = _37_164.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _37_164.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv))))
end
| t' -> begin
t'
end)
in (

let _37_169 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.tk = _37_169.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _37_169.FStar_Syntax_Syntax.vars})))
end))


let tag_lid_with_range = (fun l s -> (match ((Prims.snd s)) with
| None -> begin
l
end
| Some (r) -> begin
(let _138_90 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r)
in (FStar_Ident.set_lid_range l _138_90))
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
| _37_193 -> begin
(

let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t'), ((compose_subst s' s))))) t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_37_213), _37_216) -> begin
(failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) (Prims.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) (Prims.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _138_115 = (let _138_113 = (subst_univ (Prims.fst s) u)
in FStar_Syntax_Syntax.Tm_type (_138_113))
in (let _138_114 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk _138_115 None _138_114)))
end
| _37_226 -> begin
(let _138_117 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t0), (s)))) _138_117))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___72 -> (match (uu___72) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _138_121 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_138_121))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| (([], None)) | ((([])::[], None)) -> begin
t
end
| _37_243 -> begin
(

let _37_244 = t
in (let _138_130 = (FStar_List.map (subst_univ (Prims.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (let _138_129 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (let _138_128 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _138_127 = (FStar_List.map (fun _37_248 -> (match (_37_248) with
| (t, imp) -> begin
(let _138_125 = (subst' s t)
in ((_138_125), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _138_126 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = _138_130; FStar_Syntax_Syntax.effect_name = _138_129; FStar_Syntax_Syntax.result_typ = _138_128; FStar_Syntax_Syntax.effect_args = _138_127; FStar_Syntax_Syntax.flags = _138_126}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| (([], None)) | ((([])::[], None)) -> begin
t
end
| _37_259 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _138_134 = (subst' s t)
in (let _138_133 = (FStar_Option.map (subst_univ (Prims.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' _138_134 _138_133)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _138_136 = (subst' s t)
in (let _138_135 = (FStar_Option.map (subst_univ (Prims.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _138_136 _138_135)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _138_137 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _138_137))
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
| FStar_Syntax_Syntax.NT (_37_289) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))


let shift_subst' = (fun n s -> (let _138_148 = (FStar_All.pipe_right (Prims.fst s) (FStar_List.map (shift_subst n)))
in ((_138_148), ((Prims.snd s)))))


let subst_binder' = (fun s _37_298 -> (match (_37_298) with
| (x, imp) -> begin
(let _138_152 = (

let _37_299 = x
in (let _138_151 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_299.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_299.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_151}))
in ((_138_152), (imp)))
end))


let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = (Prims.parse_int "0")) then begin
(subst_binder' s b)
end else begin
(let _138_157 = (shift_subst' i s)
in (subst_binder' _138_157 b))
end))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (None)) bs))


let subst_arg' = (fun s _37_310 -> (match (_37_310) with
| (t, imp) -> begin
(let _138_164 = (subst' s t)
in ((_138_164), (imp)))
end))


let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range Prims.option)  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_37_320) -> begin
((p), (n))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _37_328 = (aux n p)
in (match (_37_328) with
| (p, m) -> begin
(

let ps = (FStar_List.map (fun p -> (let _138_177 = (aux n p)
in (Prims.fst _138_177))) ps)
in (((

let _37_331 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _37_331.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_331.FStar_Syntax_Syntax.p})), (m)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _37_348 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _37_339 _37_342 -> (match (((_37_339), (_37_342))) with
| ((pats, n), (p, imp)) -> begin
(

let _37_345 = (aux n p)
in (match (_37_345) with
| (p, m) -> begin
(((((p), (imp)))::pats), (m))
end))
end)) (([]), (n))))
in (match (_37_348) with
| (pats, n) -> begin
(((

let _37_349 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _37_349.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_349.FStar_Syntax_Syntax.p})), (n))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _37_354 = x
in (let _138_180 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_354.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_354.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_180}))
in (((

let _37_357 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _37_357.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_357.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _37_362 = x
in (let _138_181 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_362.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_362.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_181}))
in (((

let _37_365 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _37_365.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_365.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _37_372 = x
in (let _138_182 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_372.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_372.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_182}))
in (

let t0 = (subst' s t0)
in (((

let _37_376 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _37_376.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_376.FStar_Syntax_Syntax.p})), (n)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (l)) -> begin
(let _138_189 = (let _138_188 = (

let _37_388 = l
in (let _138_187 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _37_388.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _138_187; FStar_Syntax_Syntax.cflags = _37_388.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _37_390 -> (match (()) with
| () -> begin
(let _138_186 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _138_186))
end))}))
in FStar_Util.Inl (_138_188))
in Some (_138_189))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk = (fun t' -> (let _138_196 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' None _138_196)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_37_396) -> begin
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
in (let _138_200 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us)
in (tag_with_range _138_200 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(let _138_204 = (let _138_203 = (let _138_202 = (subst' s t0)
in (let _138_201 = (subst_args' s args)
in ((_138_202), (_138_201))))
in FStar_Syntax_Syntax.Tm_app (_138_203))
in (mk _138_204))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inl (t1), lopt) -> begin
(let _138_209 = (let _138_208 = (let _138_207 = (subst' s t0)
in (let _138_206 = (let _138_205 = (subst' s t1)
in FStar_Util.Inl (_138_205))
in ((_138_207), (_138_206), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_138_208))
in (mk _138_209))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inr (c), lopt) -> begin
(let _138_214 = (let _138_213 = (let _138_212 = (subst' s t0)
in (let _138_211 = (let _138_210 = (subst_comp' s c)
in FStar_Util.Inr (_138_210))
in ((_138_212), (_138_211), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_138_213))
in (mk _138_214))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n = (FStar_List.length bs)
in (

let s' = (shift_subst' n s)
in (let _138_219 = (let _138_218 = (let _138_217 = (subst_binders' s bs)
in (let _138_216 = (subst' s' body)
in (let _138_215 = (push_subst_lcomp s' lopt)
in ((_138_217), (_138_216), (_138_215)))))
in FStar_Syntax_Syntax.Tm_abs (_138_218))
in (mk _138_219))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n = (FStar_List.length bs)
in (let _138_224 = (let _138_223 = (let _138_222 = (subst_binders' s bs)
in (let _138_221 = (let _138_220 = (shift_subst' n s)
in (subst_comp' _138_220 comp))
in ((_138_222), (_138_221))))
in FStar_Syntax_Syntax.Tm_arrow (_138_223))
in (mk _138_224)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x = (

let _37_454 = x
in (let _138_225 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_454.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_454.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_225}))
in (

let phi = (let _138_226 = (shift_subst' (Prims.parse_int "1") s)
in (subst' _138_226 phi))
in (mk (FStar_Syntax_Syntax.Tm_refine (((x), (phi)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t0 = (subst' s t0)
in (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _37_466 -> (match (_37_466) with
| (pat, wopt, branch) -> begin
(

let _37_469 = (subst_pat' s pat)
in (match (_37_469) with
| (pat, n) -> begin
(

let s = (shift_subst' n s)
in (

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _138_228 = (subst' s w)
in Some (_138_228))
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

let lbd = if (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)) then begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end else begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let _37_491 = x
in {FStar_Syntax_Syntax.ppname = _37_491.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_491.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((

let _37_495 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _37_497 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _37_497.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = _37_497.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _37_495.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _37_495.FStar_Syntax_Syntax.fv_qual}))
end)
in (

let _37_500 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _37_500.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _37_500.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (mk (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs))), (body)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _138_234 = (let _138_233 = (let _138_232 = (subst' s t0)
in (let _138_231 = (let _138_230 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_138_230))
in ((_138_232), (_138_231))))
in FStar_Syntax_Syntax.Tm_meta (_138_233))
in (mk _138_234))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t)) -> begin
(let _138_240 = (let _138_239 = (let _138_238 = (subst' s t0)
in (let _138_237 = (let _138_236 = (let _138_235 = (subst' s t)
in ((m), (_138_235)))
in FStar_Syntax_Syntax.Meta_monadic (_138_236))
in ((_138_238), (_138_237))))
in FStar_Syntax_Syntax.Tm_meta (_138_239))
in (mk _138_240))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t)) -> begin
(let _138_246 = (let _138_245 = (let _138_244 = (subst' s t0)
in (let _138_243 = (let _138_242 = (let _138_241 = (subst' s t)
in ((m1), (m2), (_138_241)))
in FStar_Syntax_Syntax.Meta_monadic_lift (_138_242))
in ((_138_244), (_138_243))))
in FStar_Syntax_Syntax.Tm_meta (_138_245))
in (mk _138_246))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _138_249 = (let _138_248 = (let _138_247 = (subst' s t)
in ((_138_247), (m)))
in FStar_Syntax_Syntax.Tm_meta (_138_248))
in (mk _138_249))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(

let t' = (let _138_252 = (push_subst s t)
in (compress _138_252))
in (

let _37_537 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _37_540 -> begin
(

let t' = (force_uvar t)
in (match (t'.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_37_543) -> begin
(compress t')
end
| _37_546 -> begin
t'
end))
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (subst' (([]), (Some ((

let _37_551 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = _37_551.FStar_Range.use_range})))) t))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (None)) t))


let closing_subst = (fun bs -> (let _138_271 = (FStar_List.fold_right (fun _37_559 _37_562 -> (match (((_37_559), (_37_562))) with
| ((x, _37_558), (subst, n)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n))))::subst), ((n + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right _138_271 Prims.fst)))


let open_binders' = (fun bs -> (

let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let _37_573 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _138_277 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_573.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_573.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_277}))
in (

let o = (let _138_278 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_138_278)
in (

let _37_579 = (aux bs' o)
in (match (_37_579) with
| (bs', o) -> begin
(((((x'), (imp)))::bs'), (o))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _138_281 = (open_binders' bs)
in (Prims.fst _138_281)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let _37_585 = (open_binders' bs)
in (match (_37_585) with
| (bs', opening) -> begin
(let _138_286 = (subst opening t)
in ((bs'), (_138_286), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let _37_592 = (open_term' bs t)
in (match (_37_592) with
| (b, t, _37_591) -> begin
((b), (t))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let _37_597 = (open_binders' bs)
in (match (_37_597) with
| (bs', opening) -> begin
(let _138_295 = (subst_comp opening t)
in ((bs'), (_138_295)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec aux_disj = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_37_604) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (_37_607) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _37_613 = p
in (let _138_308 = (let _138_307 = (let _138_306 = (FStar_All.pipe_right pats (FStar_List.map (fun _37_617 -> (match (_37_617) with
| (p, b) -> begin
(let _138_305 = (aux_disj sub renaming p)
in ((_138_305), (b)))
end))))
in ((fv), (_138_306)))
in FStar_Syntax_Syntax.Pat_cons (_138_307))
in {FStar_Syntax_Syntax.v = _138_308; FStar_Syntax_Syntax.ty = _37_613.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_613.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let yopt = (FStar_Util.find_map renaming (fun uu___73 -> (match (uu___73) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| _37_625 -> begin
None
end)))
in (

let y = (match (yopt) with
| None -> begin
(

let _37_628 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _138_310 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_628.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_628.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_310}))
end
| Some (y) -> begin
y
end)
in (

let _37_633 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = _37_633.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_633.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _37_637 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _138_311 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_637.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_637.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_311}))
in (

let _37_640 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _37_640.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_640.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _37_646 = x
in (let _138_312 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_646.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_646.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_312}))
in (

let t0 = (subst sub t0)
in (

let _37_650 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _37_650.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_650.FStar_Syntax_Syntax.p})))
end))
in (

let rec aux = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_37_659) -> begin
((p), (sub), (renaming))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _37_668 = (aux sub renaming p)
in (match (_37_668) with
| (p, sub, renaming) -> begin
(

let ps = (FStar_List.map (aux_disj sub renaming) ps)
in (((

let _37_670 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _37_670.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_670.FStar_Syntax_Syntax.p})), (sub), (renaming)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _37_690 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _37_679 _37_682 -> (match (((_37_679), (_37_682))) with
| ((pats, sub, renaming), (p, imp)) -> begin
(

let _37_686 = (aux sub renaming p)
in (match (_37_686) with
| (p, sub, renaming) -> begin
(((((p), (imp)))::pats), (sub), (renaming))
end))
end)) (([]), (sub), (renaming))))
in (match (_37_690) with
| (pats, sub, renaming) -> begin
(((

let _37_691 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _37_691.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_691.FStar_Syntax_Syntax.p})), (sub), (renaming))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let _37_695 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _138_321 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_695.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_695.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_321}))
in (

let sub = (let _138_322 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_138_322)
in (((

let _37_699 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _37_699.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_699.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _37_703 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _138_323 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_703.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_703.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_323}))
in (

let sub = (let _138_324 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_138_324)
in (((

let _37_707 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _37_707.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_707.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _37_713 = x
in (let _138_325 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_713.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_713.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_325}))
in (

let t0 = (subst sub t0)
in (((

let _37_717 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _37_717.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_717.FStar_Syntax_Syntax.p})), (sub), (renaming))))
end))
in (

let _37_723 = (aux [] [] p)
in (match (_37_723) with
| (p, sub, _37_722) -> begin
((p), (sub))
end)))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _37_727 -> (match (_37_727) with
| (p, wopt, e) -> begin
(

let _37_730 = (open_pat p)
in (match (_37_730) with
| (p, opening) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _138_328 = (subst opening w)
in Some (_138_328))
end)
in (

let e = (subst opening e)
in ((p), (wopt), (e))))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _138_333 = (closing_subst bs)
in (subst _138_333 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _138_338 = (closing_subst bs)
in (subst_comp _138_338 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| ((x, imp))::tl -> begin
(

let x = (

let _37_750 = x
in (let _138_345 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_750.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_750.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_345}))
in (

let s' = (let _138_346 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_138_346)
in (let _138_347 = (aux s' tl)
in (((x), (imp)))::_138_347)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let _37_757 = lc
in (let _138_354 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _37_757.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _138_354; FStar_Syntax_Syntax.cflags = _37_757.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _37_759 -> (match (()) with
| () -> begin
(let _138_353 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _138_353))
end))}))))


let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_37_767) -> begin
((p), (sub))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _37_775 = (aux sub p)
in (match (_37_775) with
| (p, sub) -> begin
(

let ps = (FStar_List.map (fun p -> (let _138_362 = (aux sub p)
in (Prims.fst _138_362))) ps)
in (((

let _37_778 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _37_778.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_778.FStar_Syntax_Syntax.p})), (sub)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _37_795 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _37_786 _37_789 -> (match (((_37_786), (_37_789))) with
| ((pats, sub), (p, imp)) -> begin
(

let _37_792 = (aux sub p)
in (match (_37_792) with
| (p, sub) -> begin
(((((p), (imp)))::pats), (sub))
end))
end)) (([]), (sub))))
in (match (_37_795) with
| (pats, sub) -> begin
(((

let _37_796 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _37_796.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_796.FStar_Syntax_Syntax.p})), (sub))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _37_800 = x
in (let _138_365 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_800.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_800.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_365}))
in (

let sub = (let _138_366 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_138_366)
in (((

let _37_804 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _37_804.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_804.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _37_808 = x
in (let _138_367 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_808.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_808.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_367}))
in (

let sub = (let _138_368 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_138_368)
in (((

let _37_812 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _37_812.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_812.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _37_818 = x
in (let _138_369 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_818.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_818.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_369}))
in (

let t0 = (subst sub t0)
in (((

let _37_822 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _37_822.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _37_822.FStar_Syntax_Syntax.p})), (sub))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _37_827 -> (match (_37_827) with
| (p, wopt, e) -> begin
(

let _37_830 = (close_pat p)
in (match (_37_830) with
| (p, closing) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _138_372 = (subst closing w)
in Some (_138_372))
end)
in (

let e = (subst closing e)
in ((p), (wopt), (e))))
end))
end))


let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let _37_843 = (let _138_377 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (

let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in ((FStar_Syntax_Syntax.UN ((((n - i)), (FStar_Syntax_Syntax.U_name (u'))))), (u'))))))
in (FStar_All.pipe_right _138_377 FStar_List.unzip))
in (match (_37_843) with
| (s, us') -> begin
((s), (us'))
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (

let _37_848 = (univ_var_opening us)
in (match (_37_848) with
| (s, us') -> begin
(

let t = (subst s t)
in ((us'), (t)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let _37_854 = (univ_var_opening us)
in (match (_37_854) with
| (s, us') -> begin
(let _138_386 = (subst_comp s c)
in ((us'), (_138_386)))
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


let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
((lbs), (t))
end else begin
(

let _37_880 = (FStar_List.fold_right (fun lb _37_873 -> (match (_37_873) with
| (i, lbs, out) -> begin
(

let x = (let _138_405 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _138_405))
in (((i + (Prims.parse_int "1"))), (((

let _37_875 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _37_875.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _37_875.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _37_875.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _37_875.FStar_Syntax_Syntax.lbdef}))::lbs), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
in (match (_37_880) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _37_892 = (FStar_List.fold_right (fun u _37_886 -> (match (_37_886) with
| (i, us, out) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name None)
in (((i + (Prims.parse_int "1"))), ((u)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (_37_892) with
| (_37_889, us, u_let_rec_opening) -> begin
(

let _37_893 = lb
in (let _138_409 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _37_893.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = _37_893.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _37_893.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _138_409}))
end)))))
in (

let t = (subst let_rec_opening t)
in ((lbs), (t))))
end))
end)


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
((lbs), (t))
end else begin
(

let _37_905 = (FStar_List.fold_right (fun lb _37_902 -> (match (_37_902) with
| (i, out) -> begin
(let _138_419 = (let _138_418 = (let _138_417 = (let _138_416 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((_138_416), (i)))
in FStar_Syntax_Syntax.NM (_138_417))
in (_138_418)::out)
in (((i + (Prims.parse_int "1"))), (_138_419)))
end)) lbs (((Prims.parse_int "0")), ([])))
in (match (_37_905) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _37_914 = (FStar_List.fold_right (fun u _37_910 -> (match (_37_910) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (_37_914) with
| (_37_912, u_let_rec_closing) -> begin
(

let _37_915 = lb
in (let _138_423 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _37_915.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _37_915.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _37_915.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _37_915.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _138_423}))
end)))))
in (

let t = (subst let_rec_closing t)
in ((lbs), (t))))
end))
end)


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _37_922 -> (match (_37_922) with
| (us, t) -> begin
(

let n = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i _37_929 -> (match (_37_929) with
| (x, _37_928) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n - i)))))
end)) binders)
in (

let t = (subst s t)
in ((us), (t))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _37_935 -> (match (_37_935) with
| (us', t) -> begin
(

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n - i)))))) us)
in (let _138_436 = (subst s t)
in ((us'), (_138_436))))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _37_947 -> (match (_37_947) with
| (x, _37_946) -> begin
FStar_Syntax_Syntax.DB ((((n - i)), (x)))
end))))))




